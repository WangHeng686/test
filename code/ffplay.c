/*
 * Copyright (c) 2003 Fabrice Bellard
 *
 * This file is part of FFmpeg.
 *
 * FFmpeg is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * FFmpeg is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with FFmpeg; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 */

/**
 * @file
 * simple media player based on the FFmpeg libraries
 */

#include "config.h"
#include "config_components.h"
#include <inttypes.h>
#include <math.h>
#include <limits.h>
#include <signal.h>
#include <stdint.h>

#include "libavutil/avstring.h"
#include "libavutil/channel_layout.h"
#include "libavutil/eval.h"
#include "libavutil/mathematics.h"
#include "libavutil/pixdesc.h"
#include "libavutil/imgutils.h"
#include "libavutil/dict.h"
#include "libavutil/fifo.h"
#include "libavutil/parseutils.h"
#include "libavutil/samplefmt.h"
#include "libavutil/time.h"
#include "libavutil/bprint.h"
#include "libavformat/avformat.h"
#include "libavdevice/avdevice.h"
#include "libswscale/swscale.h"
#include "libavutil/opt.h"
#include "libavcodec/avfft.h"
#include "libswresample/swresample.h"

#if CONFIG_AVFILTER
# include "libavfilter/avfilter.h"
# include "libavfilter/buffersink.h"
# include "libavfilter/buffersrc.h"
#endif

#include <SDL.h>
#include <SDL_thread.h>

#include "cmdutils.h"
#include "opt_common.h"

const char program_name[] = "ffplay";  // 程序名称
const int program_birth_year = 2003;    // 程序创建年份

// 最大队列大小，单位为字节
#define MAX_QUEUE_SIZE (15 * 1024 * 1024) // 最大队列大小设置为15MB
#define MIN_FRAMES 25                      // 最小帧数
#define EXTERNAL_CLOCK_MIN_FRAMES 2       // 外部时钟最小帧数
#define EXTERNAL_CLOCK_MAX_FRAMES 10      // 外部时钟最大帧数

/* 最小SDL音频缓冲区大小，单位为样本 */
#define SDL_AUDIO_MIN_BUFFER_SIZE 512      // SDL音频缓冲区的最小大小设置为512样本
/* 计算实际缓冲区大小，避免音频回调过于频繁 */
#define SDL_AUDIO_MAX_CALLBACKS_PER_SEC 30 // 每秒最多30次音频回调

/* 音量控制的步长，单位为分贝 */
#define SDL_VOLUME_STEP (0.75)              // 音量调整步长设置为0.75dB

/* AV同步的最小阈值，如果低于该值则不进行同步校正 */
#define AV_SYNC_THRESHOLD_MIN 0.04          // 最小AV同步阈值设置为0.04秒
/* AV同步的最大阈值，如果高于该值则进行同步校正 */
#define AV_SYNC_THRESHOLD_MAX 0.1           // 最大AV同步阈值设置为0.1秒
/* 如果帧持续时间超过该值，则不会复制以补偿AV同步 */
#define AV_SYNC_FRAMEDUP_THRESHOLD 0.1      // 帧重复阈值设置为0.1秒
/* 如果错误过大，则不进行AV同步校正 */
#define AV_NOSYNC_THRESHOLD 10.0             // 最大不同步阈值设置为10秒

/* 最大音频速度变化，用于获得正确的同步 */
#define SAMPLE_CORRECTION_PERCENT_MAX 10    // 最大音频速度变化百分比为10%

/* 外部时钟速度调整常量，基于缓冲区满度，适用于实时源 */
#define EXTERNAL_CLOCK_SPEED_MIN  0.900     // 外部时钟最小速度为0.900
#define EXTERNAL_CLOCK_SPEED_MAX  1.010     // 外部时钟最大速度为1.010
#define EXTERNAL_CLOCK_SPEED_STEP 0.001      // 外部时钟速度调整步长为0.001

/* 我们使用大约 AUDIO_DIFF_AVG_NB 个 A-V 差异来计算平均值 */
#define AUDIO_DIFF_AVG_NB   20               // 用于计算音视频差异平均值的样本数量

/* 至少每隔这个时间轮询可能需要的屏幕刷新，应该小于1/fps */
#define REFRESH_RATE 0.01                     // 刷新率设置为0.01秒

/* 注意：大小必须足够大，以补偿硬件音频缓冲区的大小 */
/* TODO: 假设解码并重新采样的帧适合这个缓冲区 */
#define SAMPLE_ARRAY_SIZE (8 * 65536)        // 样本数组大小设置为8 * 65536

#define CURSOR_HIDE_DELAY 1000000             // 光标隐藏延迟设置为1秒（1000000微秒）

#define USE_ONEPASS_SUBTITLE_RENDER 1         // 是否使用一次性字幕渲染
static unsigned sws_flags = SWS_BICUBIC;   // 设置缩放转换标志为双立方插值


typedef struct MyAVPacketList {
    AVPacket* pkt;   // 指向AVPacket的指针，存储音视频数据包
    int serial;      // 数据包序列号，用于标识包的来源或版本,可以用于在多个流中区分数据包的来源，确保正确的同步和处理。
} MyAVPacketList;


typedef struct PacketQueue {
    AVFifo* pkt_list;      // 指向FIFO队列的指针，用于存储数据包
    int nb_packets;        // 当前队列中的数据包数量
    int size;              // 队列中所有数据包的总大小（字节）
    int64_t duration;      // 队列中所有数据包的总持续时间
    int abort_request;     // 请求停止标志，用于线程控制
    int serial;            // 数据包序列号，用于标识包的来源或版本
    SDL_mutex* mutex;      // 用于保护访问队列的互斥锁
    SDL_cond* cond;        // 条件变量，用于线程间同步
} PacketQueue;


#define VIDEO_PICTURE_QUEUE_SIZE 3        // 视频画面队列大小设置为3
#define SUBPICTURE_QUEUE_SIZE 16           // 字幕队列大小设置为16
#define SAMPLE_QUEUE_SIZE 9                 // 音频样本队列大小设置为9
#define FRAME_QUEUE_SIZE FFMAX(SAMPLE_QUEUE_SIZE, FFMAX(VIDEO_PICTURE_QUEUE_SIZE, SUBPICTURE_QUEUE_SIZE)) // 计算帧队列大小，取三个队列大小的最大值

typedef struct AudioParams {
    int freq;                     // 音频采样频率（如44100Hz）
    AVChannelLayout ch_layout;    // 音频通道布局（如立体声、单声道等）
    enum AVSampleFormat fmt;      // 音频样本格式（如16位整数、浮点数等）
    int frame_size;               // 每帧样本的大小
    int bytes_per_sec;            // 每秒的字节数（比特率）
} AudioParams;

typedef struct Clock {
    double pts;           // 当前时钟基准时间（时间戳）
    double pts_drift;     // 时钟漂移，基准时间与更新时间的差值
    double last_updated;  // 上次更新时间
    double speed;         // 时钟（播放）速度（用于调整播放速度）
    int serial;           // 与时钟相关的数据包序列号
    int paused;           // 暂停标志，指示时钟是否处于暂停状态
    int* queue_serial;    // 当前队列序列号的指针，用于检测过时的时钟
} Clock;


typedef struct Frame {
    AVFrame* frame;         // 指向解码后的视频或音频帧
    AVSubtitle sub;         // 字幕数据
    int serial;             // 与帧相关的数据包序列号
    double pts;             // 帧的显示时间戳
    double duration;        // 帧的估计持续时间
    int64_t pos;            // 帧在输入文件中的字节位置
    int width;              // 帧的宽度（仅适用于视频）
    int height;             // 帧的高度（仅适用于视频）
    int format;             // 帧的格式（如像素格式）
    AVRational sar;         // 宽高比，用于显示比例调整
    int uploaded;           // 帧是否已上传到GPU的标志
    int flip_v;             // 垂直翻转标志，指示帧是否需要翻转
} Frame;

typedef struct FrameQueue {
    Frame queue[FRAME_QUEUE_SIZE]; // 帧队列，存储多个Frame结构
    int rindex;                    // 读取索引，指示下一个要读取的帧
    int windex;                    // 写入索引，指示下一个要写入的帧
    int size;                      // 当前队列中的帧数量
    int max_size;                 // 队列的最大容量
    int keep_last;                // 标志，指示是否保留最后一帧
    int rindex_shown;             // 显示索引，指示已显示的帧的索引
    SDL_mutex* mutex;             // 互斥锁，用于保护队列的并发访问
    SDL_cond* cond;               // 条件变量，用于线程间同步
    PacketQueue* pktq;            // 指向相关数据包队列的指针
} FrameQueue;

enum {
    AV_SYNC_AUDIO_MASTER,   // 默认选择：以音频为主进行同步
    AV_SYNC_VIDEO_MASTER,   // 以视频为主进行同步
    AV_SYNC_EXTERNAL_CLOCK,  // 同步到外部时钟
};

typedef struct Decoder {
    AVPacket* pkt;                     // 指向当前解码数据包的指针
    PacketQueue* queue;                // 指向帧队列的指针，管理解码后的帧
    AVCodecContext* avctx;             // 指向编解码上下文的指针，包含解码器的配置信息
    int pkt_serial;                     // 当前数据包的序列号，用于同步
    int finished;                       // 标志，指示解码器是否已完成解码
    int packet_pending;                 // 标志，指示是否还有待处理的数据包
    SDL_cond* empty_queue_cond;        // 条件变量，控制队列为空时的同步
    int64_t start_pts;                  // 解码开始时的显示时间戳（PTS）
    AVRational start_pts_tb;            // start_pts的时间基准
    int64_t next_pts;                   // 下一个帧的显示时间戳（PTS）
    AVRational next_pts_tb;             // next_pts的时间基准
    SDL_Thread* decoder_tid;            // 解码器线程的标识
} Decoder;

//VideoState 结构体是 FFplay 中的核心组件，负责管理视频播放的状态、解码和同步。
typedef struct VideoState {
    SDL_Thread* read_tid;                 // 读取线程标识符，用于异步读取输入流
    const AVInputFormat* iformat;         // 输入格式，指示所使用的输入格式类型
    int abort_request;                     // 请求终止播放的标志
    int force_refresh;                     // 强制刷新标志，指示是否强制刷新显示
    int paused;                            // 播放状态，指示是否暂停
    int last_paused;                       // 上一次的暂停状态
    int queue_attachments_req;             // 请求附加流的标志
    int seek_req;                          // 请求查找标志
    int seek_flags;                        // 查找标志的额外参数
    int64_t seek_pos;                      // 查找的绝对位置
    int64_t seek_rel;                      // 查找的相对位置
    int read_pause_return;                 // 读取暂停的返回值
    AVFormatContext* ic;                   // 媒体格式上下文，存储流的信息
    int realtime;                          // 指示是否实时播放

    Clock audclk;                         // 音频时钟，用于同步音频播放
    Clock vidclk;                         // 视频时钟，用于同步视频播放
    Clock extclk;                         // 外部时钟，用于外部设备的同步

    FrameQueue pictq;                     // 视频帧队列
    FrameQueue subpq;                      // 字幕帧队列
    FrameQueue sampq;                     // 音频帧队列

    Decoder auddec;                       // 音频解码器
    Decoder viddec;                       // 视频解码器
    Decoder subdec;                       // 字幕解码器

    int audio_stream;                     // 当前音频流的索引

    int av_sync_type;                     // 音视频同步的类型

    double audio_clock;                   // 音频时钟，记录当前音频的时间戳
    int audio_clock_serial;               // 当前音频时钟的序列号，用于同步
    double audio_diff_cum;                // 用于音频差异计算的累积值
    double audio_diff_avg_coef;           // 音频差异平均系数
    double audio_diff_threshold;          // 音频差异阈值
    int audio_diff_avg_count;             // 音频差异平均计数
    AVStream* audio_st;                   // 指向音频流的指针
    PacketQueue audioq;                   // 音频数据包队列
    int audio_hw_buf_size;                // 音频硬件缓冲区大小
    uint8_t* audio_buf;                   // 音频缓冲区
    uint8_t* audio_buf1;                  // 辅助音频缓冲区
    unsigned int audio_buf_size;          // 音频缓冲区大小（字节）
    unsigned int audio_buf1_size;         // 辅助音频缓冲区大小
    int audio_buf_index;                  // 当前音频缓冲区索引（字节）
    int audio_write_buf_size;             // 写入音频的缓冲区大小
    int audio_volume;                      // 音量
    int muted;                             // 静音标志
    struct AudioParams audio_src;         // 源音频参数
#if CONFIG_AVFILTER         //条件编译，CONFIG_AVFILTER 是一个宏，如果它被定义（通常在编译时通过编译器选项或配置文件定义），则表示启用了音频过滤功能。
    struct AudioParams audio_filter_src;  // 过滤器输入音频参数
#endif
    struct AudioParams audio_tgt;         // 目标音频参数
    struct SwrContext* swr_ctx;           // 音频重采样上下文
    int frame_drops_early;                // 提前丢帧计数
    int frame_drops_late;                 // 延迟丢帧计数

    enum ShowMode {
        SHOW_MODE_NONE = -1,   // 不显示任何内容
        SHOW_MODE_VIDEO = 0,   // 显示视频内容
        SHOW_MODE_WAVES,       // 显示音频波形图
        SHOW_MODE_RDFT,        // 显示反离散傅里叶变换（RDFT）的结果
        SHOW_MODE_NB           // 显示模式的数量（用于枚举的边界）
    } show_mode;                          // 显示模式，定义了多种显示方式
    int16_t sample_array[SAMPLE_ARRAY_SIZE]; // 存储音频样本的数组s
    int sample_array_index;               // 当前样本数组索引
    int last_i_start;                     // 上一次开始的索引
    RDFTContext* rdft;                    // 反离散傅里叶变换上下文
    int rdft_bits;                        // 傅里叶变换位数
    FFTSample* rdft_data;                 // 傅里叶变换数据
    int xpos;                             // 当前X坐标
    double last_vis_time;                 // 上一次可视化时间
    SDL_Texture* vis_texture;             // 可视化纹理
    SDL_Texture* sub_texture;             // 字幕纹理
    SDL_Texture* vid_texture;             // 视频纹理

    int subtitle_stream;                  // 当前字幕流索引
    AVStream* subtitle_st;                // 指向字幕流的指针
    PacketQueue subtitleq;                // 字幕数据包队列

    double frame_timer;                   // 帧计时器
    double frame_last_returned_time;      // 上次返回的帧时间
    double frame_last_filter_delay;       // 上一帧的滤镜延迟
    int video_stream;                     // 当前视频流索引
    AVStream* video_st;                   // 指向视频流的指针
    PacketQueue videoq;                   // 视频数据包队列
    double max_frame_duration;            // 帧的最大持续时间
    struct SwsContext* img_convert_ctx;   // 图像转换上下文
    struct SwsContext* sub_convert_ctx;   // 字幕转换上下文
    int eof;                              // 文件结束标志

    char* filename;                       // 文件名
    int width, height, xleft, ytop;      // 视频窗口位置和尺寸
    int step;                            // 步进值

#if CONFIG_AVFILTER
    int vfilter_idx;                      // 视频过滤器索引
    AVFilterContext* in_video_filter;     // 视频链中的第一个过滤器
    AVFilterContext* out_video_filter;    // 视频链中的最后一个过滤器
    AVFilterContext* in_audio_filter;     // 音频链中的第一个过滤器
    AVFilterContext* out_audio_filter;    // 音频链中的最后一个过滤器
    AVFilterGraph* agraph;                // 音频过滤器图
#endif

    int last_video_stream, last_audio_stream, last_subtitle_stream; // 上次流索引

    SDL_cond* continue_read_thread;       // 控制读取线程继续的条件变量
} VideoState;


//输入格式与文件名
static const AVInputFormat* file_iformat;  // 用户指定的输入格式
static const char* input_filename;          // 输入文件名
static const char* window_title;             // 窗口标题
//窗口尺寸与位置
static int default_width = 640;            // 默认宽度
static int default_height = 480;            // 默认高度
static int screen_width = 0;                // 屏幕宽度
static int screen_height = 0;                // 屏幕高度
static int screen_left = SDL_WINDOWPOS_CENTERED;  // 屏幕左边距
static int screen_top = SDL_WINDOWPOS_CENTERED;   // 屏幕顶部距
//音视频流的启用与禁用
static int audio_disable;                     // 禁用音频标志
static int video_disable;                     // 禁用视频标志
static int subtitle_disable;                  // 禁用字幕标志
//流规格与寻址方式
static const char* wanted_stream_spec[AVMEDIA_TYPE_NB] = { 0 };  // 用户想要的流规格
static int seek_by_bytes = -1;                // 按字节寻址标志
static float seek_interval = 10;               // 寻址时间间隔
static int display_disable;                    // 禁用显示标志
//窗口特性与行为
static int borderless;                         // 无边框标志
static int alwaysontop;                       // 总在最上方标志
static int startup_volume = 100;              // 启动音量
static int show_status = -1;                   // 显示状态标志
//音视频同步与时间
static int av_sync_type = AV_SYNC_AUDIO_MASTER;  // 音视频同步类型
static int64_t start_time = AV_NOPTS_VALUE;     // 开始时间
static int64_t duration = AV_NOPTS_VALUE;       // 持续时间
//播放设置与标志
static int fast = 0;                           // 快速播放标志
static int genpts = 0;                         // 生成PTS标志
static int lowres = 0;                         // 低分辨率标志
//解码器与显示模式设置
static int decoder_reorder_pts = -1;          // 解码器PTS重排序
static int autoexit;                           // 自动退出标志
static int exit_on_keydown;                    // 按键退出标志
static int exit_on_mousedown;                   // 鼠标点击退出标志
static int loop = 1;                           // 循环播放标志
static int framedrop = -1;                     // 帧丢弃标志
static int infinite_buffer = -1;               // 无限缓冲标志
static enum ShowMode show_mode = SHOW_MODE_NONE;  // 显示模式
//编解码器名称
static const char* audio_codec_name;          // 音频编解码器名称
static const char* subtitle_codec_name;       // 字幕编解码器名称
static const char* video_codec_name;          // 视频编解码器名称
//光标与时间管理
double rdftspeed = 0.02;                      // RDFT速度
static int64_t cursor_last_shown;             // 上次显示光标的时间
static int cursor_hidden = 0;                  // 光标隐藏标志
//条件编译的部分
#if CONFIG_AVFILTER
static const char** vfilters_list = NULL;     // 视频过滤器列表
static int nb_vfilters = 0;                    // 视频过滤器数量
static char* afilters = NULL;                   // 音频过滤器
#endif
//自动旋转与流信息查找
static int autorotate = 1;                   // 自动旋转标志，默认为开启
static int find_stream_info = 1;              // 查找流信息的标志，默认为开启
static int filter_nbthreads = 0;              // 过滤器线程数，默认为0，表示单线程
//当前上下文
static int is_full_screen;                    // 全屏标志
static int64_t audio_callback_time;           // 音频回调时间，用于同步

#define FF_QUIT_EVENT    (SDL_USEREVENT + 2)  // 定义一个自定义的退出事件
//SDL窗口和渲染器
static SDL_Window* window;                    // SDL窗口指针
static SDL_Renderer* renderer;                // SDL渲染器指针
static SDL_RendererInfo renderer_info = { 0 };  // 渲染器信息，初始化为0
static SDL_AudioDeviceID audio_dev;           // 音频设备标识符

//像素格式与纹理格式映射
static const struct TextureFormatEntry {
    enum AVPixelFormat format;                  // FFmpeg的像素格式
    int texture_fmt;                            // SDL的纹理格式
} sdl_texture_format_map[] = {
    { AV_PIX_FMT_RGB8,           SDL_PIXELFORMAT_RGB332 },
    { AV_PIX_FMT_RGB444,         SDL_PIXELFORMAT_RGB444 },
    { AV_PIX_FMT_RGB555,         SDL_PIXELFORMAT_RGB555 },
    { AV_PIX_FMT_BGR555,         SDL_PIXELFORMAT_BGR555 },
    { AV_PIX_FMT_RGB565,         SDL_PIXELFORMAT_RGB565 },
    { AV_PIX_FMT_BGR565,         SDL_PIXELFORMAT_BGR565 },
    { AV_PIX_FMT_RGB24,          SDL_PIXELFORMAT_RGB24 },
    { AV_PIX_FMT_BGR24,          SDL_PIXELFORMAT_BGR24 },
    { AV_PIX_FMT_0RGB32,         SDL_PIXELFORMAT_RGB888 },
    { AV_PIX_FMT_0BGR32,         SDL_PIXELFORMAT_BGR888 },
    { AV_PIX_FMT_NE(RGB0, 0BGR), SDL_PIXELFORMAT_RGBX8888 },
    { AV_PIX_FMT_NE(BGR0, 0RGB), SDL_PIXELFORMAT_BGRX8888 },
    { AV_PIX_FMT_RGB32,          SDL_PIXELFORMAT_ARGB8888 },
    { AV_PIX_FMT_RGB32_1,        SDL_PIXELFORMAT_RGBA8888 },
    { AV_PIX_FMT_BGR32,          SDL_PIXELFORMAT_ABGR8888 },
    { AV_PIX_FMT_BGR32_1,        SDL_PIXELFORMAT_BGRA8888 },
    { AV_PIX_FMT_YUV420P,        SDL_PIXELFORMAT_IYUV },
    { AV_PIX_FMT_YUYV422,        SDL_PIXELFORMAT_YUY2 },
    { AV_PIX_FMT_UYVY422,        SDL_PIXELFORMAT_UYVY },
    { AV_PIX_FMT_NONE,           SDL_PIXELFORMAT_UNKNOWN },
};

#if CONFIG_AVFILTER
static int opt_add_vfilter(void* optctx, const char* opt, const char* arg)
{
    GROW_ARRAY(vfilters_list, nb_vfilters);  // 动态增长视频过滤器数组
    vfilters_list[nb_vfilters - 1] = arg;    // 添加新的过滤器
    return 0;                                 // 返回成功
}
#endif


// 定义一个比较音频格式的内联函数，以确保在处理或混合音频数据时，格式兼容性得以保持。
static inline int cmp_audio_fmts(enum AVSampleFormat fmt1, int64_t channel_count1,
    enum AVSampleFormat fmt2, int64_t channel_count2) {
    // 如果两个音频格式的通道数量都是1
    if (channel_count1 == 1 && channel_count2 == 1) {
        // 比较它们的打包样本格式
        // av_get_packed_sample_fmt(fmt) 函数获取给定样本格式的打包格式
        // 返回值为非零表示不同，0表示相同
        return av_get_packed_sample_fmt(fmt1) != av_get_packed_sample_fmt(fmt2);
    }
    else {
        // 对于通道数量不相同的情况，或者样本格式不相同
        // 返回值为非零表示不同，0表示相同
        return channel_count1 != channel_count2 || fmt1 != fmt2;
    }
}

//将音频或视频包添加到指定的队列中，执行低级的队列操作，不加锁。
static int packet_queue_put_private(PacketQueue* q, AVPacket* pkt) {
    MyAVPacketList pkt1;  // 自定义结构体，用于保存音频/视频包的信息
    int ret;              // 用于存储函数返回值

    // 检查队列是否要求终止请求，如果是，则返回 -1
    if (q->abort_request)
        return -1;

    // 设置 pkt1 的包和序列号
    pkt1.pkt = pkt;  // 将传入的包指针赋值给 pkt1
    pkt1.serial = q->serial;  // 将队列的序列号赋值给 pkt1

    // 将 pkt1 写入 FIFO 队列中
    ret = av_fifo_write(q->pkt_list, &pkt1, 1);
    if (ret < 0)  // 如果写入失败，返回错误码
        return ret;

    // 更新队列中的统计信息
    q->nb_packets++;  // 包的数量增加
    q->size += pkt1.pkt->size + sizeof(pkt1);  // 更新队列大小，包含包的大小和结构体的大小
    q->duration += pkt1.pkt->duration;  // 更新队列中所有包的总持续时间

    // 发出条件信号，唤醒等待该条件的线程
    SDL_CondSignal(q->cond);
    return 0;  // 成功添加包，返回 0
}

//处理包的分配和复制，将其放入队列中，并在需要时加锁以保护线程安全。
static int packet_queue_put(PacketQueue* q, AVPacket* pkt) {
    AVPacket* pkt1;  // 指向新分配的包
    int ret;         // 用于存储返回值

    // 分配一个新的 AVPacket，用于复制数据
    pkt1 = av_packet_alloc();
    if (!pkt1) {  // 如果分配失败
        av_packet_unref(pkt);  // 释放原始包
        return -1;  // 返回错误
    }

    // 复制原始包的数据到新分配的包
    av_packet_move_ref(pkt1, pkt);  // 移动引用，避免数据复制

    // 锁定互斥量以保护队列的操作
    SDL_LockMutex(q->mutex);
    ret = packet_queue_put_private(q, pkt1);  // 调用私有函数packet_queue_put_private，将包添加到队列
    SDL_UnlockMutex(q->mutex);  // 解锁互斥量

    // 检查返回值，如果出错则释放 pkt1
    if (ret < 0)
        av_packet_free(&pkt1);

    return ret;  // 返回操作的结果
}

//此函数用于将一个“空”数据包（通常用于表示流中的某个位置）放入指定的包队列中，同时设置流索引。
static int packet_queue_put_nullpacket(PacketQueue* q, AVPacket* pkt, int stream_index)
{
    pkt->stream_index = stream_index;  // 设置数据包的流索引
    return packet_queue_put(q, pkt);   // 将数据包放入队列
}

//初始化包队列，包括分配内存、创建互斥锁和条件变量。如果任何操作失败，则返回相应的错误代码。
static int packet_queue_init(PacketQueue* q)
{
    memset(q, 0, sizeof(PacketQueue));  // 清零包队列结构体
    q->pkt_list = av_fifo_alloc2(1, sizeof(MyAVPacketList), AV_FIFO_FLAG_AUTO_GROW); // 初始化FIFO
    if (!q->pkt_list)
        return AVERROR(ENOMEM);  // 内存分配失败

    q->mutex = SDL_CreateMutex();  // 创建互斥锁
    if (!q->mutex) {
        av_log(NULL, AV_LOG_FATAL, "SDL_CreateMutex(): %s\n", SDL_GetError());
        return AVERROR(ENOMEM);  // 错误处理
    }

    q->cond = SDL_CreateCond();  // 创建条件变量
    if (!q->cond) {
        av_log(NULL, AV_LOG_FATAL, "SDL_CreateCond(): %s\n", SDL_GetError());
        return AVERROR(ENOMEM);  // 错误处理
    }

    q->abort_request = 1;  // 初始状态设置为请求中止
    return 0;  // 成功
}

//清空包队列中的所有数据包，释放相关资源，并重置队列的状态。
static void packet_queue_flush(PacketQueue* q)
{
    MyAVPacketList pkt1;

    SDL_LockMutex(q->mutex);  // 锁定互斥量以保护数据

    // 释放队列中的所有数据包
    while (av_fifo_read(q->pkt_list, &pkt1, 1) >= 0)
        av_packet_free(&pkt1.pkt);

    q->nb_packets = 0;  // 重置包计数
    q->size = 0;        // 重置队列大小
    q->duration = 0;    // 重置持续时间
    q->serial++;        // 增加序列号
    SDL_UnlockMutex(q->mutex);  // 解锁互斥量
}

//销毁包队列，释放相关资源。
static void packet_queue_destroy(PacketQueue* q)
{
    packet_queue_flush(q);  // 先清空队列
    av_fifo_freep2(&q->pkt_list);  // 释放FIFO
    SDL_DestroyMutex(q->mutex);  // 销毁互斥量
    SDL_DestroyCond(q->cond);    // 销毁条件变量
}

//设置包队列的中止请求状态，并通知可能在等待此队列的线程。
static void packet_queue_abort(PacketQueue* q)
{
    SDL_LockMutex(q->mutex);  // 锁定互斥量
    q->abort_request = 1;  // 设置中止请求标志
    SDL_CondSignal(q->cond);  // 通知等待的线程
    SDL_UnlockMutex(q->mutex);  // 解锁互斥量
}

//重新启动包队列，允许数据包的处理。
static void packet_queue_start(PacketQueue* q)
{
    SDL_LockMutex(q->mutex);  // 锁定互斥量
    q->abort_request = 0;  // 清除中止请求标志
    q->serial++;           // 增加序列号
    SDL_UnlockMutex(q->mutex);  // 解锁互斥量
}

//从包队列中获取一个数据包。如果请求中止，返回-1；如果没有包且不阻塞，返回0；如果成功读取，返回1。
static int packet_queue_get(PacketQueue* q, AVPacket* pkt, int block, int* serial)
{
    MyAVPacketList pkt1;
    int ret;

    SDL_LockMutex(q->mutex);  // 锁定互斥量

    for (;;) {
        if (q->abort_request) {
            ret = -1;  // 如果请求中止，返回-1
            break;
        }

        if (av_fifo_read(q->pkt_list, &pkt1, 1) >= 0) {
            q->nb_packets--;  // 减少包计数
            q->size -= pkt1.pkt->size + sizeof(pkt1);  // 减少队列大小
            q->duration -= pkt1.pkt->duration;  // 减少持续时间
            av_packet_move_ref(pkt, pkt1.pkt);  // 移动数据包引用
            if (serial)
                *serial = pkt1.serial;  // 传递序列号
            av_packet_free(&pkt1.pkt);  // 释放已读数据包
            ret = 1;  // 成功读取数据包
            break;
        }
        else if (!block) {
            ret = 0;  // 非阻塞模式且没有包可读，返回0
            break;
        }
        else {
            SDL_CondWait(q->cond, q->mutex);  // 等待条件信号
        }
    }
    SDL_UnlockMutex(q->mutex);  // 解锁互斥量
    return ret;  // 返回读取状态
}

//初始化解码器实例，分配必要的资源并设置相关参数以准备解码过程。
static int decoder_init(Decoder* d, AVCodecContext* avctx, PacketQueue* queue, SDL_cond* empty_queue_cond) {
    memset(d, 0, sizeof(Decoder));  // 将解码器结构体 d 清零，确保没有残留数据

    d->pkt = av_packet_alloc();  // 为解码器分配一个 AVPacket
    if (!d->pkt)  // 检查内存分配是否成功
        return AVERROR(ENOMEM);  // 失败则返回内存不足错误代码

    d->avctx = avctx;  // 保存传入的 AVCodecContext，用于解码操作
    d->queue = queue;  // 保存传入的包队列，用于获取待解码的数据包
    d->empty_queue_cond = empty_queue_cond;  // 保存用于条件变量的指针，以便在队列为空时等待

    d->start_pts = AV_NOPTS_VALUE;  // 初始化起始时间戳为无效值
    d->pkt_serial = -1;  // 初始化数据包序列号为-1，表示尚未设置

    return 0;  // 成功初始化，返回0
}

//用于从解码器的包队列中获取包并解码成音视频帧，处理不同类型的音视频数据，并管理解码过程中的状态与时间戳。
static int decoder_decode_frame(Decoder* d, AVFrame* frame, AVSubtitle* sub) {
    int ret = AVERROR(EAGAIN);  // 初始返回值设为EAGAIN

    for (;;) {
        // 如果当前包序列与解码器序列匹配
        if (d->queue->serial == d->pkt_serial) {
            do {
                if (d->queue->abort_request)  // 检查是否请求中止
                    return -1;

                // 根据解码类型处理视频或音频
                switch (d->avctx->codec_type) {
                case AVMEDIA_TYPE_VIDEO:  // 视频解码
                    ret = avcodec_receive_frame(d->avctx, frame);
                    if (ret >= 0) {
                        // 设置帧时间戳
                        if (decoder_reorder_pts == -1) {
                            frame->pts = frame->best_effort_timestamp;// 如果禁用时间戳重排序，使用最佳努力时间戳
                        }
                        else if (!decoder_reorder_pts) {
                            frame->pts = frame->pkt_dts;// 如果未启用重排序，使用包的解码时间戳
                        }
                    }
                    break;
                case AVMEDIA_TYPE_AUDIO:  // 音频解码
                    ret = avcodec_receive_frame(d->avctx, frame);
                    if (ret >= 0) {
                        AVRational tb = (AVRational){ 1, frame->sample_rate };  // 创建一个表示时间基的结构，单位为样本/秒
                        // 设置音频帧时间戳
                        if (frame->pts != AV_NOPTS_VALUE)// 如果当前帧的时间戳有效，使用它
                            frame->pts = av_rescale_q(frame->pts, d->avctx->pkt_timebase, tb); // 将帧的时间戳从解码器的时间基转换到音频帧的时间基
                        else if (d->next_pts != AV_NOPTS_VALUE)// 如果当前帧没有有效时间戳，但下一个时间戳有效，使用下一个时间戳
                            frame->pts = av_rescale_q(d->next_pts, d->next_pts_tb, tb);

                        if (frame->pts != AV_NOPTS_VALUE) { // 如果帧的时间戳有效，更新下一帧的时间戳和时间基
                            d->next_pts = frame->pts + frame->nb_samples;   // 下一帧的时间戳为当前时间戳加上样本数量
                            d->next_pts_tb = tb;// 保存当前帧的时间基以供下一帧使用
                        }
                    }
                    break;
                }
                if (ret == AVERROR_EOF) {  // 检查是否解码完成
                    d->finished = d->pkt_serial;
                    avcodec_flush_buffers(d->avctx);  // 清空解码器缓冲
                    return 0;
                }
                if (ret >= 0)  // 成功解码一帧
                    return 1;
            } while (ret != AVERROR(EAGAIN));  // 继续解码直到没有更多数据
        }

        // 获取新包以继续解码
        do {
            if (d->queue->nb_packets == 0)//如果当前队列中没有包
                SDL_CondSignal(d->empty_queue_cond);  // 信号通知空队列
            if (d->packet_pending) {//如果有包处于挂起状态（d->packet_pending），则将其状态重置，表示当前的挂起包已被处理。
                d->packet_pending = 0;  // 处理挂起的包
            }
            else {//否则获取新报
                int old_serial = d->pkt_serial;//先保存当前包的序列号
                if (packet_queue_get(d->queue, d->pkt, 1, &d->pkt_serial) < 0)//调用packet_queue_get从队列中获取一个新包，更新当前包的序列号
                    return -1;  
                if (old_serial != d->pkt_serial) {  // 如果获取到的新包序列号与旧的不同，意味着已切换到新的包。
                    avcodec_flush_buffers(d->avctx);  // 需要清空解码器的缓冲（avcodec_flush_buffers），并重置时间戳相关的变量。
                    d->finished = 0;
                    d->next_pts = d->start_pts;  // 重置时间戳
                    d->next_pts_tb = d->start_pts_tb;
                }
            }
            if (d->queue->serial == d->pkt_serial)  // 确保队列和解码器序列一致
                break;
            av_packet_unref(d->pkt);  // 释放当前包
        } while (1);

        // 处理字幕解码
        if (d->avctx->codec_type == AVMEDIA_TYPE_SUBTITLE) {//检查解码器的编码类型是否为字幕
            int got_frame = 0;//指示是否成功解码出字幕帧。
            ret = avcodec_decode_subtitle2(d->avctx, sub, &got_frame, d->pkt);  // 解码字幕
            if (ret < 0) {
                ret = AVERROR(EAGAIN);  // 如果需要更多数据
            }
            else {
                if (got_frame && !d->pkt->data) {// 如果成功解码但没有数据
                    d->packet_pending = 1;      //则标记packet_pending为1，表示有包待处理。
                }
                ret = got_frame ? 0 : (d->pkt->data ? AVERROR(EAGAIN) : AVERROR_EOF);
            }
            av_packet_unref(d->pkt);  // 释放当前包，以防止内存泄漏
        }
        else {
            // 处理音频/视频包的发送
            if (avcodec_send_packet(d->avctx, d->pkt) == AVERROR(EAGAIN)) {
                av_log(d->avctx, AV_LOG_ERROR, "Receive_frame and send_packet both returned EAGAIN, which is an API violation.\n");
                d->packet_pending = 1;  // 标记为待处理
            }
            else {
                av_packet_unref(d->pkt);  // 释放当前包
            }
        }
    }
}

//用于释放Decoder结构体中分配的资源
static void decoder_destroy(Decoder* d) {
    av_packet_free(&d->pkt);  // 释放与解码器关联的AVPacket结构，确保不再使用的包数据被正确释放。
    avcodec_free_context(&d->avctx);  // 释放与解码器上下文相关的资源，清理解码器状态和设置。
}

//释放一个Frame结构中的帧和字幕资源，确保不再使用的帧数据被正确清理。
static void frame_queue_unref_item(Frame* vp) {
    av_frame_unref(vp->frame);  // 解除帧的引用，释放与该帧相关的内存。
    avsubtitle_free(&vp->sub);  // 释放字幕结构体的内存，确保字幕数据被妥善清理。
}

//初始化一个帧队列，分配必要的资源，包括互斥锁和条件变量，以及创建用于存储帧的内存。
static int frame_queue_init(FrameQueue* f, PacketQueue* pktq, int max_size, int keep_last) {
    int i;
    memset(f, 0, sizeof(FrameQueue));  // 将帧队列结构体初始化为零。

    // 创建互斥锁
    if (!(f->mutex = SDL_CreateMutex())) {
        av_log(NULL, AV_LOG_FATAL, "SDL_CreateMutex(): %s\n", SDL_GetError());
        return AVERROR(ENOMEM);  // 内存分配错误
    }

    // 创建条件变量
    if (!(f->cond = SDL_CreateCond())) {
        av_log(NULL, AV_LOG_FATAL, "SDL_CreateCond(): %s\n", SDL_GetError());
        return AVERROR(ENOMEM);  // 内存分配错误
    }

    // 设置队列的相关属性
    f->pktq = pktq;  // 关联数据包队列
    f->max_size = FFMIN(max_size, FRAME_QUEUE_SIZE);  // 确保最大尺寸不超过预设值
    f->keep_last = !!keep_last;  // 设置是否保留最后一帧的标志

    // 为帧队列中的每个元素分配帧内存
    for (i = 0; i < f->max_size; i++)
        if (!(f->queue[i].frame = av_frame_alloc()))  // 分配AVFrame
            return AVERROR(ENOMEM);  // 内存分配错误

    return 0;  // 初始化成功
}

//释放帧队列中所有帧的资源，并清理互斥锁和条件变量。
static void frame_queue_destroy(FrameQueue* f) {
    int i;
    // 释放帧队列中的每个帧
    for (i = 0; i < f->max_size; i++) {
        Frame* vp = &f->queue[i];  // 获取当前帧
        frame_queue_unref_item(vp);  // 释放帧和字幕的内存
        av_frame_free(&vp->frame);  // 释放AVFrame的内存
    }

    // 销毁互斥锁和条件变量
    SDL_DestroyMutex(f->mutex);
    SDL_DestroyCond(f->cond);
}

//发出信号以通知等待该条件变量的线程，表示可以进行下一步操作。
static void frame_queue_signal(FrameQueue* f) {
    SDL_LockMutex(f->mutex);  // 锁定互斥锁，确保线程安全
    SDL_CondSignal(f->cond);  // 发出条件变量信号，唤醒一个等待的线程
    SDL_UnlockMutex(f->mutex);  // 解锁互斥锁
}

//返回队列中当前要读取的帧的指针。
static Frame *frame_queue_peek(FrameQueue *f)
{
    return &f->queue[((f->rindex + f->rindex_shown) % f->max_size]; // 返回队列中当前读取索引位置的帧，使用环形队列计算索引
}
//返回队列中下一个要读取的帧的指针
static Frame *frame_queue_peek_next(FrameQueue *f)
{
    return &f->queue[(f->rindex + f->rindex_shown + 1) % f->max_size];// 返回下一个将要读取的帧，索引向后偏移一个位置
}
//返回队列中最后一帧的指针
static Frame *frame_queue_peek_last(FrameQueue *f)
{
    return &f->queue[f->rindex];// 返回当前读取索引位置的帧，通常是最后一帧
}

//等待并返回一个可写入的帧的指针，确保在添加新帧之前队列中有空间。
static Frame* frame_queue_peek_writable(FrameQueue* f) {
    // 等待直到队列中有空间可以写入新帧
    SDL_LockMutex(f->mutex);  // 锁定互斥锁

    // 循环等待，直到队列不满或请求被中止
    while (f->size >= f->max_size && !f->pktq->abort_request) {
        SDL_CondWait(f->cond, f->mutex);  // 等待条件变量信号
    }

    SDL_UnlockMutex(f->mutex);  // 解锁互斥锁

    // 如果接收到中止请求，返回NULL
    if (f->pktq->abort_request)
        return NULL;

    // 返回可写入帧的指针
    return &f->queue[f->windex];  // 返回写入索引位置的帧
}

//等待并返回可读的帧的指针，确保在读取帧之前队列中有可读帧。
static Frame* frame_queue_peek_readable(FrameQueue* f) {
    // 等待直到队列中有可读帧
    SDL_LockMutex(f->mutex);  // 锁定互斥锁以确保线程安全

    // 循环等待，直到队列中有可读帧或请求被中止
    while (f->size - f->rindex_shown <= 0 && !f->pktq->abort_request) {
        SDL_CondWait(f->cond, f->mutex);  // 等待条件变量信号
    }

    SDL_UnlockMutex(f->mutex);  // 解锁互斥锁

    // 如果接收到中止请求，返回NULL
    if (f->pktq->abort_request)
        return NULL;

    // 返回可读帧的指针，使用环形队列计算索引
    return &f->queue[(f->rindex + f->rindex_shown) % f->max_size];
}

//将新帧推入队列，并更新写入索引。
static void frame_queue_push(FrameQueue* f) {
    // 更新写入索引，若超出最大大小则回绕
    if (++f->windex == f->max_size)
        f->windex = 0;

    SDL_LockMutex(f->mutex);  // 锁定互斥锁以确保线程安全
    f->size++;  // 增加队列大小
    SDL_CondSignal(f->cond);  // 发出条件变量信号，通知其他线程有新帧可用
    SDL_UnlockMutex(f->mutex);  // 解锁互斥锁
}

//更新读取索引，准备读取下一帧。
static void frame_queue_next(FrameQueue* f) {
    // 如果保持最后一帧且当前未显示，标记为已显示
    if (f->keep_last && !f->rindex_shown) {
        f->rindex_shown = 1;  // 标记已显示
        return;  // 返回，不更新索引
    }

    // 释放当前帧资源
    frame_queue_unref_item(&f->queue[f->rindex]);

    // 更新读取索引，若超出最大大小则回绕
    if (++f->rindex == f->max_size)
        f->rindex = 0;

    SDL_LockMutex(f->mutex);  // 锁定互斥锁以确保线程安全
    f->size--;  // 减少队列大小
    SDL_CondSignal(f->cond);  // 发出条件变量信号，通知其他线程可能有可写空间
    SDL_UnlockMutex(f->mutex);  // 解锁互斥锁
}


//返回队列中剩余的帧数量
static int frame_queue_nb_remaining(FrameQueue *f)
{
    return f->size - f->rindex_shown;// 计算并返回尚未显示的帧数
}

//返回队列中最后一个显示的帧的位置
static int64_t frame_queue_last_pos(FrameQueue *f)
{
    Frame *fp = &f->queue[f->rindex];// 获取当前读取索引指向的帧
    if (f->rindex_shown && fp->serial == f->pktq->serial)// 检查当前帧是否已显示且序列号与包队列的序列号一致
        return fp->pos;// 返回当前帧的位置
    else
        return -1;
}

//中止解码器，清理资源并等待线程结束。
static void decoder_abort(Decoder* d, FrameQueue* fq) {
    packet_queue_abort(d->queue);  // 中止数据包队列
    frame_queue_signal(fq);  // 通知帧队列，可能有新状态
    SDL_WaitThread(d->decoder_tid, NULL);  // 等待解码线程结束
    d->decoder_tid = NULL;  // 重置解码线程ID
    packet_queue_flush(d->queue);  // 清空数据包队列
}

//在给定位置绘制一个矩形
static inline void fill_rectangle(int x, int y, int w, int h) {
    SDL_Rect rect;  // 创建SDL矩形结构
    rect.x = x;  // 设置矩形的x坐标
    rect.y = y;  // 设置矩形的y坐标
    rect.w = w;  // 设置矩形的宽度
    rect.h = h;  // 设置矩形的高度

    // 如果宽度和高度都大于0，则绘制矩形
    if (w && h)
        SDL_RenderFillRect(renderer, &rect);  // 使用SDL渲染函数填充矩形
}

//重新分配并创建一个SDL纹理，确保其格式和大小与给定参数一致。
static int realloc_texture(SDL_Texture** texture, Uint32 new_format, int new_width, int new_height, SDL_BlendMode blendmode, int init_texture) {
    Uint32 format;  // 当前纹理格式
    int access, w, h;  // 访问类型和当前宽高

    // 检查是否需要重新创建纹理
    if (!*texture || SDL_QueryTexture(*texture, &format, &access, &w, &h) < 0 || new_width != w || new_height != h || new_format != format) {
        void* pixels;  // 纹理像素数据指针
        int pitch;  // 行宽度

        if (*texture)  // 如果已有纹理，销毁之
            SDL_DestroyTexture(*texture);

        // 创建新的纹理
        if (!(*texture = SDL_CreateTexture(renderer, new_format, SDL_TEXTUREACCESS_STREAMING, new_width, new_height)))
            return -1;  
        // 设置纹理的混合模式
        if (SDL_SetTextureBlendMode(*texture, blendmode) < 0)
            return -1;  
        // 如果需要初始化纹理
        if (init_texture) {
            // 锁定纹理以访问像素数据
            if (SDL_LockTexture(*texture, NULL, &pixels, &pitch) < 0)
                return -1;  
            // 将纹理像素数据清零
            memset(pixels, 0, pitch * new_height);
            SDL_UnlockTexture(*texture);  // 解锁纹理
        }

        // 日志记录创建的纹理信息
        av_log(NULL, AV_LOG_VERBOSE, "Created %dx%d texture with %s.\n", new_width, new_height, SDL_GetPixelFormatName(new_format));
    }
    return 0;  // 返回成功
}

//计算显示矩形的坐标和尺寸，确保保持图像的宽高比
static void calculate_display_rect(SDL_Rect *rect,
                                   int scr_xleft, int scr_ytop, int scr_width, int scr_height,
                                   int pic_width, int pic_height, AVRational pic_sar) {
    AVRational aspect_ratio = pic_sar;  // 图像的宽高比
    int64_t width, height, x, y;

    // 如果宽高比无效，则设置为1:1
    if (av_cmp_q(aspect_ratio, av_make_q(0, 1)) <= 0)
        aspect_ratio = av_make_q(1, 1);

    // 计算实际的宽高比
    aspect_ratio = av_mul_q(aspect_ratio, av_make_q(pic_width, pic_height));

    // 假设屏幕的像素比为1.0
    height = scr_height;
    width = av_rescale(height, aspect_ratio.num, aspect_ratio.den) & ~1;  // 按高度计算宽度并取整为偶数
    if (width > scr_width) {  // 如果计算的宽度超过屏幕宽度
        width = scr_width;
        height = av_rescale(width, aspect_ratio.den, aspect_ratio.num) & ~1;  // 按宽度计算高度
    }
    
    // 计算矩形的显示位置
    x = (scr_width - width) / 2;  // 居中显示
    y = (scr_height - height) / 2;
    rect->x = scr_xleft + x;  // 更新矩形的x坐标
    rect->y = scr_ytop + y;    // 更新矩形的y坐标
    rect->w = FFMAX((int)width,  1);  // 确保宽度至少为1
    rect->h = FFMAX((int)height, 1);  // 确保高度至少为1
}

//根据给定的格式返回SDL所需的像素格式和混合模式
static void get_sdl_pix_fmt_and_blendmode(int format, Uint32* sdl_pix_fmt, SDL_BlendMode* sdl_blendmode) {
    int i;
    *sdl_blendmode = SDL_BLENDMODE_NONE;  // 默认混合模式为无
    *sdl_pix_fmt = SDL_PIXELFORMAT_UNKNOWN;  // 默认像素格式为未知

    // 根据格式设置混合模式
    if (format == AV_PIX_FMT_RGB32 || format == AV_PIX_FMT_RGB32_1 ||
        format == AV_PIX_FMT_BGR32 || format == AV_PIX_FMT_BGR32_1)
        *sdl_blendmode = SDL_BLENDMODE_BLEND;  // 设置为可混合模式

    // 遍历纹理格式映射表，找到对应的SDL像素格式
    for (i = 0; i < FF_ARRAY_ELEMS(sdl_texture_format_map) - 1; i++) {
        if (format == sdl_texture_format_map[i].format) {
            *sdl_pix_fmt = sdl_texture_format_map[i].texture_fmt;  // 设置对应的SDL像素格式
            return;  // 找到匹配格式后返回
        }
    }
}

//将一个AVFrame（视频帧）上传到SDL纹理中，根据帧的像素格式进行相应处理
static int upload_texture(SDL_Texture** tex, AVFrame* frame, struct SwsContext** img_convert_ctx) {
    int ret = 0;  // 返回值初始化为0，表示成功
    Uint32 sdl_pix_fmt;  // SDL像素格式
    SDL_BlendMode sdl_blendmode;  // SDL混合模式

    // 获取SDL像素格式和混合模式
    get_sdl_pix_fmt_and_blendmode(frame->format, &sdl_pix_fmt, &sdl_blendmode);

    // 重新分配纹理
    if (realloc_texture(tex, sdl_pix_fmt == SDL_PIXELFORMAT_UNKNOWN ? SDL_PIXELFORMAT_ARGB8888 : sdl_pix_fmt, frame->width, frame->height, sdl_blendmode, 0) < 0)
        return -1;  // 如果重新分配失败，返回错误

    // 根据像素格式处理上传逻辑
    switch (sdl_pix_fmt) {
    case SDL_PIXELFORMAT_UNKNOWN:
        // 如果未定义的格式，通常是在不使用avfilter的情况下
        *img_convert_ctx = sws_getCachedContext(*img_convert_ctx,
            frame->width, frame->height, frame->format, frame->width, frame->height,
            AV_PIX_FMT_BGRA, sws_flags, NULL, NULL, NULL);
        if (*img_convert_ctx != NULL) {
            uint8_t* pixels[4];  // 存储像素数据的指针数组
            int pitch[4];  // 存储每行的字节数
            if (!SDL_LockTexture(*tex, NULL, (void**)pixels, pitch)) {
                // 进行像素格式转换并上传纹理
                sws_scale(*img_convert_ctx, (const uint8_t* const*)frame->data, frame->linesize,
                    0, frame->height, pixels, pitch);
                SDL_UnlockTexture(*tex);  // 解锁纹理
            }
        }
        else {
            av_log(NULL, AV_LOG_FATAL, "Cannot initialize the conversion context\n");
            ret = -1;  // 初始化失败，设置返回值
        }
        break;

    case SDL_PIXELFORMAT_IYUV:
        // 对于YUV格式的帧，检查行大小并更新纹理
        if (frame->linesize[0] > 0 && frame->linesize[1] > 0 && frame->linesize[2] > 0) {
            ret = SDL_UpdateYUVTexture(*tex, NULL, frame->data[0], frame->linesize[0],
                frame->data[1], frame->linesize[1],
                frame->data[2], frame->linesize[2]);
        }
        else if (frame->linesize[0] < 0 && frame->linesize[1] < 0 && frame->linesize[2] < 0) {
            ret = SDL_UpdateYUVTexture(*tex, NULL,
                frame->data[0] + frame->linesize[0] * (frame->height - 1), -frame->linesize[0],
                frame->data[1] + frame->linesize[1] * (AV_CEIL_RSHIFT(frame->height, 1) - 1), -frame->linesize[1],
                frame->data[2] + frame->linesize[2] * (AV_CEIL_RSHIFT(frame->height, 1) - 1), -frame->linesize[2]);
        }
        else {
            av_log(NULL, AV_LOG_ERROR, "Mixed negative and positive linesizes are not supported.\n");
            return -1;  // 混合正负行大小不支持，返回错误
        }
        break;

    default:
        // 对于其他格式的帧，直接更新纹理
        if (frame->linesize[0] < 0) {
            ret = SDL_UpdateTexture(*tex, NULL, frame->data[0] + frame->linesize[0] * (frame->height - 1), -frame->linesize[0]);
        }
        else {
            ret = SDL_UpdateTexture(*tex, NULL, frame->data[0], frame->linesize[0]);
        }
        break;
    }
    return ret;  // 返回上传结果
}

//设置SDL的YUV转换模式，以便正确处理不同格式的YUV图像。
static void set_sdl_yuv_conversion_mode(AVFrame* frame) {
#if SDL_VERSION_ATLEAST(2,0,8)
    SDL_YUV_CONVERSION_MODE mode = SDL_YUV_CONVERSION_AUTOMATIC;  // 默认YUV转换模式
    if (frame && (frame->format == AV_PIX_FMT_YUV420P || frame->format == AV_PIX_FMT_YUYV422 || frame->format == AV_PIX_FMT_UYVY422)) {
        // 根据帧的颜色范围和色彩空间设置转换模式
        if (frame->color_range == AVCOL_RANGE_JPEG)
            mode = SDL_YUV_CONVERSION_JPEG;
        else if (frame->colorspace == AVCOL_SPC_BT709)
            mode = SDL_YUV_CONVERSION_BT709;
        else if (frame->colorspace == AVCOL_SPC_BT470BG || frame->colorspace == AVCOL_SPC_SMPTE170M)
            mode = SDL_YUV_CONVERSION_BT601;
    }
    SDL_SetYUVConversionMode(mode);  // 应用设置的YUV转换模式
#endif
}

//在SDL中显示视频帧和字幕，根据当前视频状态更新显示内容
static void video_image_display(VideoState* is) {
    Frame* vp;  // 当前视频帧
    Frame* sp = NULL;  // 当前字幕帧
    SDL_Rect rect;  // 用于显示的矩形区域

    // 获取帧队列中的最新视频帧
    vp = frame_queue_peek_last(&is->pictq);

    // 检查是否有字幕流
    if (is->subtitle_st) {
        // 如果字幕队列中有剩余字幕
        if (frame_queue_nb_remaining(&is->subpq) > 0) {
            sp = frame_queue_peek(&is->subpq);  // 获取当前字幕帧

            // 判断视频帧的PTS是否超过当前字幕的显示时间
            if (vp->pts >= sp->pts + ((float)sp->sub.start_display_time / 1000)) {
                // 如果字幕尚未上传
                if (!sp->uploaded) {
                    uint8_t* pixels[4];  // 存储像素数据的指针数组
                    int pitch[4];  // 存储每行的字节数
                    int i;

                    // 初始化字幕帧的宽高
                    if (!sp->width || !sp->height) {
                        sp->width = vp->width;
                        sp->height = vp->height;
                    }

                    // 重新分配字幕纹理
                    if (realloc_texture(&is->sub_texture, SDL_PIXELFORMAT_ARGB8888, sp->width, sp->height, SDL_BLENDMODE_BLEND, 1) < 0)
                        return;  // 失败则返回

                    // 遍历所有字幕矩形
                    for (i = 0; i < sp->sub.num_rects; i++) {
                        AVSubtitleRect* sub_rect = sp->sub.rects[i];

                        // 限制字幕矩形的位置和大小
                        sub_rect->x = av_clip(sub_rect->x, 0, sp->width);
                        sub_rect->y = av_clip(sub_rect->y, 0, sp->height);
                        sub_rect->w = av_clip(sub_rect->w, 0, sp->width - sub_rect->x);
                        sub_rect->h = av_clip(sub_rect->h, 0, sp->height - sub_rect->y);

                        // 初始化转换上下文
                        is->sub_convert_ctx = sws_getCachedContext(is->sub_convert_ctx,
                            sub_rect->w, sub_rect->h, AV_PIX_FMT_PAL8,
                            sub_rect->w, sub_rect->h, AV_PIX_FMT_BGRA,
                            0, NULL, NULL, NULL);
                        if (!is->sub_convert_ctx) {
                            av_log(NULL, AV_LOG_FATAL, "Cannot initialize the conversion context\n");
                            return;  // 初始化失败，返回
                        }

                        // 锁定纹理并进行转换
                        if (!SDL_LockTexture(is->sub_texture, (SDL_Rect*)sub_rect, (void**)pixels, pitch)) {
                            sws_scale(is->sub_convert_ctx, (const uint8_t* const*)sub_rect->data, sub_rect->linesize,
                                0, sub_rect->h, pixels, pitch);
                            SDL_UnlockTexture(is->sub_texture);  // 解锁纹理
                        }
                    }
                    sp->uploaded = 1;  // 标记为已上传
                }
            }
            else {
                sp = NULL;  // 如果不满足条件，清空字幕帧
            }
        }
    }

    // 计算显示矩形
    calculate_display_rect(&rect, is->xleft, is->ytop, is->width, is->height, vp->width, vp->height, vp->sar);

    // 设置YUV转换模式
    set_sdl_yuv_conversion_mode(vp->frame);

    // 上传视频帧到纹理
    if (!vp->uploaded) {
        if (upload_texture(&is->vid_texture, vp->frame, &is->img_convert_ctx) < 0) {
            set_sdl_yuv_conversion_mode(NULL);
            return;  // 上传失败，返回
        }
        vp->uploaded = 1;  // 标记为已上传
        vp->flip_v = vp->frame->linesize[0] < 0;  // 根据行大小判断是否翻转
}

    // 在SDL中绘制视频纹理
    SDL_RenderCopyEx(renderer, is->vid_texture, NULL, &rect, 0, NULL, vp->flip_v ? SDL_FLIP_VERTICAL : 0);
    set_sdl_yuv_conversion_mode(NULL);  // 恢复YUV模式

    // 绘制字幕
    if (sp) {
#if USE_ONEPASS_SUBTITLE_RENDER
        SDL_RenderCopy(renderer, is->sub_texture, NULL, &rect);  // 一次性绘制
#else
        int i;
        double xratio = (double)rect.w / (double)sp->width;  // 计算宽比
        double yratio = (double)rect.h / (double)sp->height;  // 计算高比

        // 遍历所有字幕矩形，调整并绘制
        for (i = 0; i < sp->sub.num_rects; i++) {
            SDL_Rect* sub_rect = (SDL_Rect*)sp->sub.rects[i];
            SDL_Rect target = { .x = rect.x + sub_rect->x * xratio,
                               .y = rect.y + sub_rect->y * yratio,
                               .w = sub_rect->w * xratio,
                               .h = sub_rect->h * yratio };
            SDL_RenderCopy(renderer, is->sub_texture, sub_rect, &target);
        }
#endif
    }
}


static inline int compute_mod(int a, int b)
{
    return a < 0 ? a%b + b : a%b;// 计算模运算，处理负数情况
}

//用于在SDL窗口中显示音频波形或频谱，基于当前的音频状态和播放进度绘制音频的视觉表示。
static void video_audio_display(VideoState* s)
{
    int i, i_start, x, y1, y, ys, delay, n, nb_display_channels;
    int ch, channels, h, h2;
    int64_t time_diff;
    int rdft_bits, nb_freq;

    // 计算RDFT的位数，确定频率分析的大小
    for (rdft_bits = 1; (1 << rdft_bits) < 2 * s->height; rdft_bits++)
        ;
    nb_freq = 1 << (rdft_bits - 1);  // 计算频率数

    // 计算显示索引：以当前输出样本为中心
    channels = s->audio_tgt.ch_layout.nb_channels;  // 获取音频通道数
    nb_display_channels = channels;  // 显示的通道数
    if (!s->paused) {  // 如果没有暂停
        int data_used = s->show_mode == SHOW_MODE_WAVES ? s->width : (2 * nb_freq);
        n = 2 * channels;  // 每个通道的样本数量
        delay = s->audio_write_buf_size;  // 获取写入缓冲区的大小
        delay /= n;  // 根据通道数计算延迟

        // 精确计算自上次缓冲计算以来的时间
        if (audio_callback_time) {
            time_diff = av_gettime_relative() - audio_callback_time;  // 计算时间差
            delay -= (time_diff * s->audio_tgt.freq) / 1000000;  // 从延迟中减去时间差
        }

        // 确保延迟不会小于使用的数据量
        delay += 2 * data_used;
        if (delay < data_used)
            delay = data_used;

        // 计算开始索引
        i_start = x = compute_mod(s->sample_array_index - delay * channels, SAMPLE_ARRAY_SIZE);
        if (s->show_mode == SHOW_MODE_WAVES) {
            h = INT_MIN;  // 初始化高度
            // 寻找波形最高点
            for (i = 0; i < 1000; i += channels) {
                int idx = (SAMPLE_ARRAY_SIZE + x - i) % SAMPLE_ARRAY_SIZE;  // 环形索引
                int a = s->sample_array[idx];
                int b = s->sample_array[(idx + 4 * channels) % SAMPLE_ARRAY_SIZE];
                int c = s->sample_array[(idx + 5 * channels) % SAMPLE_ARRAY_SIZE];
                int d = s->sample_array[(idx + 9 * channels) % SAMPLE_ARRAY_SIZE];
                int score = a - d;  // 计算当前波形的得分
                // 更新开始索引
                if (h < score && (b ^ c) < 0) {
                    h = score;
                    i_start = idx;
                }
            }
        }

        s->last_i_start = i_start;  // 保存最后的开始索引
    }
    else {
        i_start = s->last_i_start;  // 如果暂停，使用上一个开始索引
    }

    if (s->show_mode == SHOW_MODE_WAVES) {  // 波形显示模式
        SDL_SetRenderDrawColor(renderer, 255, 255, 255, 255);  // 设置绘图颜色为白色

        // 计算每个通道的总高度
        h = s->height / nb_display_channels;
        // 计算图形高度的一半
        h2 = (h * 9) / 20;
        for (ch = 0; ch < nb_display_channels; ch++) {  // 遍历每个通道
            i = i_start + ch;  // 当前样本索引
            y1 = s->ytop + ch * h + (h / 2);  // 中心线位置
            for (x = 0; x < s->width; x++) {  // 遍历宽度
                y = (s->sample_array[i] * h2) >> 15;  // 计算Y坐标
                if (y < 0) {
                    y = -y;
                    ys = y1 - y;  // 向上绘制
                }
                else {
                    ys = y1;  // 向下绘制
                }
                fill_rectangle(s->xleft + x, ys, 1, y);  // 绘制矩形表示波形
                i += channels;  // 移动到下一个样本
                if (i >= SAMPLE_ARRAY_SIZE)  // 环绕处理
                    i -= SAMPLE_ARRAY_SIZE;
            }
        }

        // 绘制通道分隔线
        SDL_SetRenderDrawColor(renderer, 0, 0, 255, 255);  // 设置颜色为蓝色
        for (ch = 1; ch < nb_display_channels; ch++) {
            y = s->ytop + ch * h;  // 计算分隔线的Y坐标
            fill_rectangle(s->xleft, y, s->width, 1);  // 绘制分隔线
        }
    }
    else {  // 频谱显示模式
        // 重新分配纹理
        if (realloc_texture(&s->vis_texture, SDL_PIXELFORMAT_ARGB8888, s->width, s->height, SDL_BLENDMODE_NONE, 1) < 0)
            return;

        if (s->xpos >= s->width)  // 如果位置超出宽度，重置为0
            s->xpos = 0;
        nb_display_channels = FFMIN(nb_display_channels, 2);  // 限制通道数为最大2
        if (rdft_bits != s->rdft_bits) {  // 如果RDFT位数变化
            av_rdft_end(s->rdft);  // 结束当前RDFT
            av_free(s->rdft_data);  // 释放旧数据
            s->rdft = av_rdft_init(rdft_bits, DFT_R2C);  // 初始化新的RDFT
            s->rdft_bits = rdft_bits;  // 更新位数
            s->rdft_data = av_malloc_array(nb_freq, 4 * sizeof(*s->rdft_data));  // 分配新数据
        }
        if (!s->rdft || !s->rdft_data) {  // 检查内存分配失败
            av_log(NULL, AV_LOG_ERROR, "Failed to allocate buffers for RDFT, switching to waves display\n");
            s->show_mode = SHOW_MODE_WAVES;  // 切换回波形显示
        }
        else {
            FFTSample* data[2];  // 存储频率数据的数组
            SDL_Rect rect = { .x = s->xpos, .y = 0, .w = 1, .h = s->height };  // 矩形区域
            uint32_t* pixels;  // 像素指针
            int pitch;  // 行间距
            for (ch = 0; ch < nb_display_channels; ch++) {  // 遍历每个通道
                data[ch] = s->rdft_data + 2 * nb_freq * ch;  // 获取通道数据
                i = i_start + ch;  // 当前样本索引
                for (x = 0; x < 2 * nb_freq; x++) {  // 遍历频率数据
                    double w = (x - nb_freq) * (1.0 / nb_freq);  // 计算权重
                    data[ch][x] = s->sample_array[i] * (1.0 - w * w);  // 计算频率样本
                    i += channels;  // 移动到下一个样本
                    if (i >= SAMPLE_ARRAY_SIZE)  // 环绕处理
                        i -= SAMPLE_ARRAY_SIZE;
                }
                av_rdft_calc(s->rdft, data[ch]);  // 计算RDFT
            }

            // 锁定纹理以更新像素
            if (!SDL_LockTexture(s->vis_texture, &rect, (void**)&pixels, &pitch)) {
                pitch >>= 2;  // 每个像素的字节数
                pixels += pitch * s->height;  // 移动到底部
                for (y = 0; y < s->height; y++) {  // 遍历高度
                    double w = 1 / sqrt(nb_freq);  // 归一化权重
                    int a = sqrt(w * sqrt(data[0][2 * y + 0] * data[0][2 * y + 0] + data[0][2 * y + 1] * data[0][2 * y + 1]));  // 计算红色分量
                    int b = (nb_display_channels == 2) ? sqrt(w * hypot(data[1][2 * y + 0], data[1][2 * y + 1])) : a;  // 计算蓝色分量
                    a = FFMIN(a, 255);  // 限制最大值为255
                    b = FFMIN(b, 255);

                    pixels -= pitch;// 移动到上一行
                    *pixels = (a << 16) + (b << 8) + ((a+b) >> 1);// 组合ARGB颜色
                }
                SDL_UnlockTexture(s->vis_texture); // 解锁纹理
            }
            SDL_RenderCopy(renderer, s->vis_texture, NULL, NULL);// 渲染纹理到屏幕
        }
        if (!s->paused)// 如果没有暂停
            s->xpos++;// 增加X位置以更新显示
    }
}

//于关闭视频流中的特定组件（音频、视频或字幕），并释放相关资源
static void stream_component_close(VideoState* is, int stream_index)
{
    AVFormatContext* ic = is->ic;  // 获取当前格式上下文
    AVCodecParameters* codecpar;    // 编解码参数指针

    // 检查流索引的有效性
    if (stream_index < 0 || stream_index >= ic->nb_streams)
        return;  // 如果无效，直接返回

    codecpar = ic->streams[stream_index]->codecpar;  // 获取指定流的编解码参数

    // 根据编解码类型进行不同的处理
    switch (codecpar->codec_type) {
    case AVMEDIA_TYPE_AUDIO:  // 音频流
        decoder_abort(&is->auddec, &is->sampq);  // 中止音频解码器
        SDL_CloseAudioDevice(audio_dev);  // 关闭音频设备
        decoder_destroy(&is->auddec);  // 销毁音频解码器
        swr_free(&is->swr_ctx);  // 释放重采样上下文
        av_freep(&is->audio_buf1);  // 释放音频缓冲区
        is->audio_buf1_size = 0;  // 重置缓冲区大小
        is->audio_buf = NULL;  // 置空缓冲区指针

        // 如果存在RDFT，进行清理
        if (is->rdft) {
            av_rdft_end(is->rdft);  // 结束RDFT
            av_freep(&is->rdft_data);  // 释放RDFT数据
            is->rdft = NULL;  // 置空RDFT指针
            is->rdft_bits = 0;  // 重置RDFT位数
        }
        break;

    case AVMEDIA_TYPE_VIDEO:  // 视频流
        decoder_abort(&is->viddec, &is->pictq);  // 中止视频解码器
        decoder_destroy(&is->viddec);  // 销毁视频解码器
        break;

    case AVMEDIA_TYPE_SUBTITLE:  // 字幕流
        decoder_abort(&is->subdec, &is->subpq);  // 中止字幕解码器
        decoder_destroy(&is->subdec);  // 销毁字幕解码器
        break;

    default:
        break;  // 其他类型不处理
    }

    // 将流的丢弃标志设置为丢弃所有数据
    ic->streams[stream_index]->discard = AVDISCARD_ALL;

    // 根据编解码类型更新流状态
    switch (codecpar->codec_type) {
    case AVMEDIA_TYPE_AUDIO:
        is->audio_st = NULL;  // 置空音频流指针
        is->audio_stream = -1;  // 重置音频流索引
        break;
    case AVMEDIA_TYPE_VIDEO:
        is->video_st = NULL;  // 置空视频流指针
        is->video_stream = -1;  // 重置视频流索引
        break;
    case AVMEDIA_TYPE_SUBTITLE:
        is->subtitle_st = NULL;  // 置空字幕流指针
        is->subtitle_stream = -1;  // 重置字幕流索引
        break;
    default:
        break;  // 其他类型不处理
    }
}

//用于安全关闭一个视频流的所有相关组件和资源，他会调用stream_component_close
static void stream_close(VideoState* is)
{
    /* 设置请求标志以中止解析过程 */
    is->abort_request = 1;
    SDL_WaitThread(is->read_tid, NULL);  // 等待读取线程结束

    /* 关闭每个流（音频、视频、字幕） */
    if (is->audio_stream >= 0)  // 如果存在音频流
        stream_component_close(is, is->audio_stream);  // 关闭音频流
    if (is->video_stream >= 0)  // 如果存在视频流
        stream_component_close(is, is->video_stream);  // 关闭视频流
    if (is->subtitle_stream >= 0)  // 如果存在字幕流
        stream_component_close(is, is->subtitle_stream);  // 关闭字幕流

    avformat_close_input(&is->ic);  // 关闭输入格式上下文

    // 销毁各个数据包队列
    packet_queue_destroy(&is->videoq);  // 销毁视频数据包队列
    packet_queue_destroy(&is->audioq);  // 销毁音频数据包队列
    packet_queue_destroy(&is->subtitleq);  // 销毁字幕数据包队列

    // 销毁所有帧队列
    frame_queue_destory(&is->pictq);  // 销毁图片帧队列
    frame_queue_destory(&is->sampq);  // 销毁音频样本队列
    frame_queue_destory(&is->subpq);  // 销毁字幕帧队列

    SDL_DestroyCond(is->continue_read_thread);  // 销毁读取线程条件变量
    sws_freeContext(is->img_convert_ctx);  // 释放图像转换上下文
    sws_freeContext(is->sub_convert_ctx);  // 释放字幕转换上下文
    av_free(is->filename);  // 释放文件名字符串
    if (is->vis_texture)  // 如果存在视觉纹理
        SDL_DestroyTexture(is->vis_texture);  // 销毁视觉纹理
    if (is->vid_texture)  // 如果存在视频纹理
        SDL_DestroyTexture(is->vid_texture);  // 销毁视频纹理
    if (is->sub_texture)  // 如果存在字幕纹理
        SDL_DestroyTexture(is->sub_texture);  // 销毁字幕纹理
    av_free(is);  // 释放 VideoState 结构体
}

//用于安全退出程序
static void do_exit(VideoState* is)
{
    if (is) {  // 如果 VideoState 指针不为空
        stream_close(is);  // 调用 stream_close 释放相关资源
    }
    if (renderer)  // 如果渲染器存在
        SDL_DestroyRenderer(renderer);  // 销毁 SDL 渲染器
    if (window)  // 如果窗口存在
        SDL_DestroyWindow(window);  // 销毁 SDL 窗口
    uninit_opts();  // 反初始化选项

#if CONFIG_AVFILTER  // 如果启用了 AVFilter
    av_freep(&vfilters_list);  // 释放过滤器列表
#endif

    avformat_network_deinit();  // 反初始化网络相关资源

    if (show_status)  // 如果需要显示状态
        printf("\n");  // 打印换行符

    SDL_Quit();  // 退出 SDL

    av_log(NULL, AV_LOG_QUIET, "%s", "");  // 记录日志，设置为安静模式

    exit(0);  // 正常退出程序
}

//信号处理函数，用于处理 SIGTERM 信号。接收到信号后，它将直接退出程序并返回状态码 123
static void sigterm_handler(int sig)
{
    exit(123);  // 处理 SIGTERM 信号，退出程序，返回状态码 123
}

//计算并设置默认窗口的大小
static void set_default_window_size(int width, int height, AVRational sar)
{
    SDL_Rect rect;  // SDL 矩形用于存储计算后的窗口尺寸
    int max_width = screen_width ? screen_width : INT_MAX;  // 获取最大宽度
    int max_height = screen_height ? screen_height : INT_MAX;  // 获取最大高度

    if (max_width == INT_MAX && max_height == INT_MAX)  // 如果最大宽度和高度都未设置
        max_height = height;  // 将最大高度设置为默认高度

    calculate_display_rect(&rect, 0, 0, max_width, max_height, width, height, sar);  // 计算显示矩形

    default_width = rect.w;  // 更新默认宽度
    default_height = rect.h;  // 更新默认高度
}


// video_open: 打开视频窗口并配置其大小、位置和标题。
static int video_open(VideoState* is) {
    int w, h;

    w = screen_width ? screen_width : default_width;  // 确定宽度，优先使用屏幕宽度
    h = screen_height ? screen_height : default_height; // 确定高度，优先使用屏幕高度

    if (!window_title)                              // 如果没有窗口标题
        window_title = input_filename;             // 将窗口标题设置为输入文件名
    SDL_SetWindowTitle(window, window_title);      // 设置窗口标题

    SDL_SetWindowSize(window, w, h);               // 设置窗口大小
    SDL_SetWindowPosition(window, screen_left, screen_top); // 设置窗口位置
    if (is_full_screen)                             // 如果需要全屏
        SDL_SetWindowFullscreen(window, SDL_WINDOW_FULLSCREEN_DESKTOP); // 切换到全屏模式
    SDL_ShowWindow(window);                         // 显示窗口

    is->width = w;                                 // 更新 VideoState 的宽度
    is->height = h;                                 // 更新 VideoState 的高度

    return 0;                                       // 返回成功标志
}

// video_display: 显示当前的视频帧或音频信息。
static void video_display(VideoState* is) {
    if (!is->width)                                // 如果宽度未初始化
        video_open(is);                            // 调用 video_open 函数

    SDL_SetRenderDrawColor(renderer, 0, 0, 0, 255); // 设置渲染器的绘制颜色为黑色
    SDL_RenderClear(renderer);                     // 清空渲染器
    if (is->audio_st && is->show_mode != SHOW_MODE_VIDEO) // 如果有音频且不显示视频
        video_audio_display(is);                   // 显示音频信息
    else if (is->video_st)                         // 如果有视频流
        video_image_display(is);                   // 显示视频帧
    SDL_RenderPresent(renderer);                   // 提交渲染结果
}

// get_clock: 获取时钟的当前值，考虑状态和序列匹配。
static double get_clock(Clock* c) {
    if (*c->queue_serial != c->serial)           // 如果时钟序列不匹配
        return NAN;                               // 返回 NaN
    if (c->paused) {                              // 如果时钟处于暂停状态
        return c->pts;                            // 返回当前时间戳
    }
    else {                                      // 如果时钟未暂停
        double time = av_gettime_relative() / 1000000.0; // 获取当前时间
        return c->pts_drift + time - (time - c->last_updated) * (1.0 - c->speed); // 计算并返回时钟值
    }
}


// set_clock_at: 设置时钟的时间戳、序列号和更新时间。
static void set_clock_at(Clock* c, double pts, int serial, double time) {
    c->pts = pts;                                   // 设置当前时间戳
    c->last_updated = time;                         // 记录最后更新时间
    c->pts_drift = c->pts - time;                  // 计算时间漂移
    c->serial = serial;                             // 设置序列号
}

// set_clock: 获取当前时间并调用 set_clock_at 设置时钟。
static void set_clock(Clock* c, double pts, int serial) {
    double time = av_gettime_relative() / 1000000.0; // 获取当前时间
    set_clock_at(c, pts, serial, time);            // 调用 set_clock_at 设置时钟
}

// set_clock_speed: 更新时钟速度，并设置当前时间戳。
static void set_clock_speed(Clock* c, double speed) {
    set_clock(c, get_clock(c), c->serial);         // 获取当前时钟值并设置
    c->speed = speed;                               // 更新时钟速度
}

// init_clock: 初始化时钟并设置初始状态。
static void init_clock(Clock* c, int* queue_serial) {
    c->speed = 1.0;                                // 设置初始速度为1.0
    c->paused = 0;                                 // 设置时钟为未暂停状态
    c->queue_serial = queue_serial;                 // 关联队列序列
    set_clock(c, NAN, -1);                         // 设置时钟为未定义状态
}

// sync_clock_to_slave: 将主时钟同步到从时钟。
static void sync_clock_to_slave(Clock* c, Clock* slave) {
    double clock = get_clock(c);                   // 获取主时钟值
    double slave_clock = get_clock(slave);         // 获取从时钟值
    // 如果从时钟有效且主时钟无效或两者差距超过阈值
    if (!isnan(slave_clock) && (isnan(clock) || fabs(clock - slave_clock) > AV_NOSYNC_THRESHOLD))
        set_clock(c, slave_clock, slave->serial); // 同步主时钟到从时钟
}


// get_master_sync_type: 获取当前主同步类型，根据视频或音频流的存在决定返回值。
static int get_master_sync_type(VideoState* is) {
    if (is->av_sync_type == AV_SYNC_VIDEO_MASTER) { // 如果主同步类型为视频
        if (is->video_st)                             // 检查是否存在视频流
            return AV_SYNC_VIDEO_MASTER;             // 返回视频主同步类型
        else
            return AV_SYNC_AUDIO_MASTER;              // 返回音频主同步类型
    }
    else if (is->av_sync_type == AV_SYNC_AUDIO_MASTER) { // 如果主同步类型为音频
        if (is->audio_st)                            // 检查是否存在音频流
            return AV_SYNC_AUDIO_MASTER;             // 返回音频主同步类型
        else
            return AV_SYNC_EXTERNAL_CLOCK;           // 返回外部时钟同步类型
    }
    else {
        return AV_SYNC_EXTERNAL_CLOCK;               // 默认返回外部时钟同步类型
    }
}

// get_master_clock: 获取当前的主时钟值，基于主同步类型。
static double get_master_clock(VideoState* is) {
    double val;

    switch (get_master_sync_type(is)) {            // 根据主同步类型获取时钟值
    case AV_SYNC_VIDEO_MASTER:
        val = get_clock(&is->vidclk);           // 从视频时钟获取值
        break;
    case AV_SYNC_AUDIO_MASTER:
        val = get_clock(&is->audclk);           // 从音频时钟获取值
        break;
    default:
        val = get_clock(&is->extclk);           // 从外部时钟获取值
        break;
    }
    return val;                                     // 返回主时钟值
}

// check_external_clock_speed: 检查并调整外部时钟的速度。
static void check_external_clock_speed(VideoState* is) {
    // 如果视频或音频流的包数少于最小帧数
    if (is->video_stream >= 0 && is->videoq.nb_packets <= EXTERNAL_CLOCK_MIN_FRAMES ||
        is->audio_stream >= 0 && is->audioq.nb_packets <= EXTERNAL_CLOCK_MIN_FRAMES) {
        set_clock_speed(&is->extclk, FFMAX(EXTERNAL_CLOCK_SPEED_MIN, is->extclk.speed - EXTERNAL_CLOCK_SPEED_STEP));
    }
    // 如果视频和音频流的包数都超过最大帧数
    else if ((is->video_stream < 0 || is->videoq.nb_packets > EXTERNAL_CLOCK_MAX_FRAMES) &&
        (is->audio_stream < 0 || is->audioq.nb_packets > EXTERNAL_CLOCK_MAX_FRAMES)) {
        set_clock_speed(&is->extclk, FFMIN(EXTERNAL_CLOCK_SPEED_MAX, is->extclk.speed + EXTERNAL_CLOCK_SPEED_STEP));
    }
    // 如果当前速度不为1.0，调整速度接近1.0
    else {
        double speed = is->extclk.speed;
        if (speed != 1.0)
            set_clock_speed(&is->extclk, speed + EXTERNAL_CLOCK_SPEED_STEP * (1.0 - speed) / fabs(1.0 - speed));
    }
}

// stream_seek: 在流中进行寻址，根据给定的位置和相对值设置寻址请求。
static void stream_seek(VideoState* is, int64_t pos, int64_t rel, int by_bytes) {
    if (!is->seek_req) {                            // 如果没有寻址请求
        is->seek_pos = pos;                        // 设置目标位置
        is->seek_rel = rel;                        // 设置相对值
        is->seek_flags &= ~AVSEEK_FLAG_BYTE;       // 清除字节标志
        if (by_bytes)                              // 如果按字节寻址
            is->seek_flags |= AVSEEK_FLAG_BYTE;   // 设置字节标志
        is->seek_req = 1;                          // 标记为寻址请求
        SDL_CondSignal(is->continue_read_thread);  // 唤醒读取线程
    }
}

// stream_toggle_pause: 暂停或恢复视频播放。
static void stream_toggle_pause(VideoState* is) {
    if (is->paused) {                              // 如果当前处于暂停状态
        is->frame_timer += av_gettime_relative() / 1000000.0 - is->vidclk.last_updated; // 更新帧定时器
        if (is->read_pause_return != AVERROR(ENOSYS)) { // 检查暂停返回值
            is->vidclk.paused = 0;                 // 恢复视频时钟
        }
        set_clock(&is->vidclk, get_clock(&is->vidclk), is->vidclk.serial); // 更新时钟
    }
    set_clock(&is->extclk, get_clock(&is->extclk), is->extclk.serial); // 更新外部时钟
    is->paused = is->audclk.paused = is->vidclk.paused = is->extclk.paused = !is->paused; // 切换暂停状态
}

// toggle_pause: 切换播放和暂停状态，并重置步进状态。
static void toggle_pause(VideoState* is) {
    stream_toggle_pause(is);                       // 调用 stream_toggle_pause 切换状态
    is->step = 0;                                  // 重置步进状态
}

// toggle_mute: 切换静音状态。
static void toggle_mute(VideoState* is) {
    is->muted = !is->muted;                        // 切换静音标志
}

// update_volume: 更新音频音量，根据给定的增量调整音量级别。
static void update_volume(VideoState* is, int sign, double step) {
    double volume_level = is->audio_volume ? (20 * log(is->audio_volume / (double)SDL_MIX_MAXVOLUME) / log(10)) : -1000.0; // 计算当前音量的分贝值
    int new_volume = lrint(SDL_MIX_MAXVOLUME * pow(10.0, (volume_level + sign * step) / 20.0)); // 计算新的音量值
    // 更新音量值，确保在合法范围内
    is->audio_volume = av_clip(is->audio_volume == new_volume ? (is->audio_volume + sign) : new_volume, 0, SDL_MIX_MAXVOLUME);
}

// step_to_next_frame: 步进到下一帧，如果流被暂停则先恢复播放。
static void step_to_next_frame(VideoState* is) {
    if (is->paused)                                  // 如果当前处于暂停状态
        stream_toggle_pause(is);                     // 切换到播放状态
    is->step = 1;                                    // 标记为步进状态
}

// compute_target_delay: 计算目标延迟以跟随主同步源的时间。
static double compute_target_delay(double delay, VideoState* is) {
    double sync_threshold, diff = 0;

    // 根据主同步源更新延迟
    if (get_master_sync_type(is) != AV_SYNC_VIDEO_MASTER) {
        // 如果视频是从属，尝试通过重复或跳过帧来修正大延迟
        diff = get_clock(&is->vidclk) - get_master_clock(is); // 计算视频时钟与主时钟的差异

        // 跳过或重复帧。考虑到延迟来计算阈值
        sync_threshold = FFMAX(AV_SYNC_THRESHOLD_MIN, FFMIN(AV_SYNC_THRESHOLD_MAX, delay));
        if (!isnan(diff) && fabs(diff) < is->max_frame_duration) {
            if (diff <= -sync_threshold)                 // 如果差异小于负阈值
                delay = FFMAX(0, delay + diff);        // 减少延迟
            else if (diff >= sync_threshold && delay > AV_SYNC_FRAMEDUP_THRESHOLD)
                delay = delay + diff;                   // 增加延迟
            else if (diff >= sync_threshold)
                delay = 2 * delay;                      // 重复帧
        }
    }

    av_log(NULL, AV_LOG_TRACE, "video: delay=%0.3f A-V=%f\n", delay, -diff); // 日志输出当前延迟和音视频差异

    return delay;                                     // 返回更新后的延迟
}


// vp_duration: 计算视频帧的持续时间，如果帧序列相同则返回有效持续时间，否则返回0。
static double vp_duration(VideoState* is, Frame* vp, Frame* nextvp) {
    if (vp->serial == nextvp->serial) {              // 检查当前帧和下一帧的序列是否相同
        double duration = nextvp->pts - vp->pts;     // 计算持续时间
        if (isnan(duration) || duration <= 0 || duration > is->max_frame_duration) // 如果持续时间无效
            return vp->duration;                       // 返回默认持续时间
        else
            return duration;                           // 返回计算得到的持续时间
    }
    else {
        return 0.0;                                   // 序列不同则返回0
    }
}

// update_video_pts: 更新当前视频的时间戳，并同步到外部时钟。
static void update_video_pts(VideoState* is, double pts, int64_t pos, int serial) {
    set_clock(&is->vidclk, pts, serial);             // 设置视频时钟的时间戳
    sync_clock_to_slave(&is->extclk, &is->vidclk);  // 将视频时钟同步到外部时钟
}


// video_refresh: 刷新视频画面，处理帧显示、音视频同步以及字幕管理
static void video_refresh(void* opaque, double* remaining_time) {
    VideoState* is = opaque;                        // 获取视频状态结构体指针
    double time;                                    // 用于存储当前时间

    Frame* sp, * sp2;                                // 用于存储字幕帧指针

    // 检查外部时钟速度（如果正在播放且不是暂停状态）
    if (!is->paused && get_master_sync_type(is) == AV_SYNC_EXTERNAL_CLOCK && is->realtime)
        check_external_clock_speed(is);             // 调整外部时钟速度以保持同步

    // 如果显示未禁用且当前模式不是视频模式，并且有音频流
    if (!display_disable && is->show_mode != SHOW_MODE_VIDEO && is->audio_st) {
        time = av_gettime_relative() / 1000000.0;  // 获取当前时间（单位：秒）
        // 如果强制刷新或上次可视时间加上刷新速率小于当前时间，则更新显示
        if (is->force_refresh || is->last_vis_time + rdftspeed < time) {
            video_display(is);                       // 调用视频显示函数
            is->last_vis_time = time;               // 更新最后一次显示时间
        }
        // 更新剩余时间，确保不超过帧的显示时间
        *remaining_time = FFMIN(*remaining_time, is->last_vis_time + rdftspeed - time);
    }

    // 如果存在视频流
    if (is->video_st) {
    retry:
        // 检查当前帧队列是否为空
        if (frame_queue_nb_remaining(&is->pictq) == 0) {
            // 如果没有帧可显示，什么也不做
        }
        else {
            double last_duration, duration, delay; // 用于存储时间持续、当前持续时间和延迟
            Frame* vp, * lastvp;                    // 用于当前帧和上一帧的指针

            /* 出队列，获取最后一帧和当前帧 */
            lastvp = frame_queue_peek_last(&is->pictq);  // 获取上一帧
            vp = frame_queue_peek(&is->pictq);            // 获取当前帧

            // 检查当前帧序列是否与视频流序列匹配
            if (vp->serial != is->videoq.serial) {
                frame_queue_next(&is->pictq);            // 不匹配则跳到下一帧
                goto retry;                              // 重试获取帧
            }

            // 如果上一帧序列与当前帧不同，重置帧定时器
            if (lastvp->serial != vp->serial)
                is->frame_timer = av_gettime_relative() / 1000000.0; // 更新帧定时器为当前时间

            // 如果当前处于暂停状态，则跳到显示阶段
            if (is->paused)
                goto display;

            /* 计算当前帧的名义持续时间 */
            last_duration = vp_duration(is, lastvp, vp); // 计算上一帧与当前帧的持续时间
            delay = compute_target_delay(last_duration, is); // 计算目标延迟

            time = av_gettime_relative() / 1000000.0;  // 获取当前时间
            // 检查是否需要等待以维持适当的延迟
            if (time < is->frame_timer + delay) {
                *remaining_time = FFMIN(is->frame_timer + delay - time, *remaining_time); // 更新剩余时间
                goto display;                            // 跳到显示阶段
            }

            is->frame_timer += delay;                   // 更新帧定时器
            // 检查延迟是否过长，若是，则将帧定时器重置为当前时间
            if (delay > 0 && time - is->frame_timer > AV_SYNC_THRESHOLD_MAX)
                is->frame_timer = time;                  // 防止时间超出最大阈值

            SDL_LockMutex(is->pictq.mutex);            // 锁定帧队列以保护共享数据
            // 如果当前帧的PTS（时间戳）有效，则更新视频时间戳
            if (!isnan(vp->pts))
                update_video_pts(is, vp->pts, vp->pos, vp->serial);
            SDL_UnlockMutex(is->pictq.mutex);          // 解锁帧队列

            // 检查队列中是否还有剩余的帧
            if (frame_queue_nb_remaining(&is->pictq) > 1) {
                Frame* nextvp = frame_queue_peek_next(&is->pictq); // 获取下一帧
                duration = vp_duration(is, vp, nextvp); // 计算当前帧与下一帧的持续时间
                // 如果不在步进模式，并且满足丢帧条件，则丢弃当前帧
                if (!is->step && (framedrop > 0 || (framedrop && get_master_sync_type(is) != AV_SYNC_VIDEO_MASTER)) && time > is->frame_timer + duration) {
                    is->frame_drops_late++;              // 记录丢帧事件
                    frame_queue_next(&is->pictq);        // 跳到下一帧
                    goto retry;                          // 重试获取帧
                }
            }

            // 处理字幕帧
            if (is->subtitle_st) {
                // 处理字幕队列中的所有字幕帧
                while (frame_queue_nb_remaining(&is->subpq) > 0) {
                    sp = frame_queue_peek(&is->subpq); // 获取当前字幕帧

                    // 获取下一字幕帧（如果存在）
                    if (frame_queue_nb_remaining(&is->subpq) > 1)
                        sp2 = frame_queue_peek_next(&is->subpq);
                    else
                        sp2 = NULL;

                    // 检查当前字幕帧是否已过期
                    if (sp->serial != is->subtitleq.serial
                        || (is->vidclk.pts > (sp->pts + ((float)sp->sub.end_display_time / 1000))) // 检查当前时间是否超过字幕结束时间
                        || (sp2 && is->vidclk.pts > (sp2->pts + ((float)sp2->sub.start_display_time / 1000)))) // 检查下一帧的起始时间
                    {
                        // 如果字幕已上传，则清除其显示区域
                        if (sp->uploaded) {
                            int i;
                            for (i = 0; i < sp->sub.num_rects; i++) {
                                AVSubtitleRect* sub_rect = sp->sub.rects[i]; // 获取字幕矩形区域
                                uint8_t* pixels;
                                int pitch, j;

                                // 锁定字幕纹理并清除其显示区域
                                if (!SDL_LockTexture(is->sub_texture, (SDL_Rect*)sub_rect, (void**)&pixels, &pitch)) {
                                    for (j = 0; j < sub_rect->h; j++, pixels += pitch)
                                        memset(pixels, 0, sub_rect->w << 2); // 清除字幕区域
                                    SDL_UnlockTexture(is->sub_texture); // 解锁纹理
                                }
                            }
                        }
                        frame_queue_next(&is->subpq);          // 跳到下一字幕帧
                    }
                    else {
                        break;                               // 如果未过期，则退出循环
                    }
                }
            }

            frame_queue_next(&is->pictq);                // 跳到下一帧以进行显示
            is->force_refresh = 1;                       // 设置强制刷新标志

            // 如果在步进模式且未暂停，则切换暂停状态
            if (is->step && !is->paused)
                stream_toggle_pause(is);
        }
    display:
        // 显示当前帧
        if (!display_disable && is->force_refresh && is->show_mode == SHOW_MODE_VIDEO && is->pictq.rindex_shown)
            video_display(is);                           // 调用视频显示函数
    }
    is->force_refresh = 0;                              // 重置强制刷新标志
    // 显示状态信息
    if (show_status) {
        AVBPrint buf;                                 // 用于格式化输出的缓冲区
        static int64_t last_time;                     // 用于记录上次输出的时间
        int64_t cur_time;                             // 当前时间
        int aqsize, vqsize, sqsize;                   // 音频、视频和字幕队列大小
        double av_diff;                               // 音视频时间差

        cur_time = av_gettime_relative();             // 获取当前时间
        // 每30秒输出一次状态信息
        if (!last_time || (cur_time - last_time) >= 30000) {
            aqsize = 0;                               // 初始化音频队列大小
            vqsize = 0;                               // 初始化视频队列大小
            sqsize = 0;                               // 初始化字幕队列大小
            if (is->audio_st)
                aqsize = is->audioq.size;          // 获取音频队列大小
            if (is->video_st)
                vqsize = is->videoq.size;          // 获取视频队列大小
            if (is->subtitle_st)
                sqsize = is->subtitleq.size;      // 获取字幕队列大小

            av_diff = 0;                           // 初始化音视频时间差
            // 根据是否存在音频流和视频流计算时间差
            if (is->audio_st && is->video_st)
                av_diff = get_clock(&is->audclk) - get_clock(&is->vidclk); // 计算音频与视频时钟的差
            else if (is->video_st)
                av_diff = get_master_clock(is) - get_clock(&is->vidclk); // 计算主时钟与视频时钟的差
            else if (is->audio_st)
                av_diff = get_master_clock(is) - get_clock(&is->audclk); // 计算主时钟与音频时钟的差

            av_bprint_init(&buf, 0, AV_BPRINT_SIZE_AUTOMATIC); // 初始化打印缓冲区
            // 格式化状态信息
            av_bprintf(&buf,
                "%7.2f %s:%7.3f fd=%4d aq=%5dKB vq=%5dKB sq=%5dB f=%"PRId64"/%"PRId64"   \r",
                get_master_clock(is),                     // 获取主时钟值
                (is->audio_st && is->video_st) ? "A-V" : (is->video_st ? "M-V" : (is->audio_st ? "M-A" : "   ")), // 状态标识
                av_diff,                                   // 音视频时间差
                is->frame_drops_early + is->frame_drops_late, // 丢帧计数
                aqsize / 1024,                             // 音频队列大小（KB）
                vqsize / 1024,                             // 视频队列大小（KB）
                sqsize,                                    // 字幕队列大小
                is->video_st ? is->viddec.avctx->pts_correction_num_faulty_dts : 0, // 视频流的DTS错误计数
                is->video_st ? is->viddec.avctx->pts_correction_num_faulty_pts : 0); // 视频流的PTS错误计数

            // 根据日志级别决定如何输出状态信息
            if (show_status == 1 && AV_LOG_INFO > av_log_get_level())
                fprintf(stderr, "%s", buf.str);        // 直接输出到标准错误
            else
                av_log(NULL, AV_LOG_INFO, "%s", buf.str); // 使用AV日志系统输出

            fflush(stderr);                           // 刷新标准错误输出
            av_bprint_finalize(&buf, NULL);          // 清理打印缓冲区
            last_time = cur_time;                     // 更新上次输出时间
        }
    }
}

/* 将视频帧入队，准备显示 */
static int queue_picture(VideoState* is, AVFrame* src_frame, double pts, double duration, int64_t pos, int serial)
{
    Frame* vp; // 定义一个指向 Frame 结构的指针

#if defined(DEBUG_SYNC)
    // 如果在调试模式下，打印帧类型和时间戳
    printf("frame_type=%c pts=%0.3f\n",
        av_get_picture_type_char(src_frame->pict_type), pts);
#endif

    // 尝试获取可写入的帧，如果失败则返回 -1
    if (!(vp = frame_queue_peek_writable(&is->pictq)))
        return -1;

    // 设置帧的宽高比、上传状态、宽高和格式
    vp->sar = src_frame->sample_aspect_ratio; // 设置样本宽高比
    vp->uploaded = 0;                           // 设置未上传标志

    vp->width = src_frame->width;               // 设置帧宽
    vp->height = src_frame->height;             // 设置帧高
    vp->format = src_frame->format;             // 设置帧格式

    // 设置帧的时间戳、持续时间、位置和序列号
    vp->pts = pts;                               // 设置显示时间戳
    vp->duration = duration;                     // 设置帧持续时间
    vp->pos = pos;                               // 设置位置
    vp->serial = serial;                         // 设置序列号

    // 根据帧的宽高和宽高比设置默认窗口大小
    set_default_window_size(vp->width, vp->height, vp->sar);

    // 移动源帧的数据到队列帧中
    av_frame_move_ref(vp->frame, src_frame);
    // 将帧推入队列
    frame_queue_push(&is->pictq);
    return 0; // 成功入队返回 0
}

/* 获取视频帧并处理 */
static int get_video_frame(VideoState* is, AVFrame* frame)
{
    int got_picture; // 定义获取帧的标志

    // 解码一帧视频，返回是否成功
    if ((got_picture = decoder_decode_frame(&is->viddec, frame, NULL)) < 0)
        return -1; // 解码失败返回 -1

    if (got_picture) { // 如果成功获取到帧
        double dpts = NAN; // 定义时间戳变量

        // 如果帧的时间戳有效，计算其显示时间
        if (frame->pts != AV_NOPTS_VALUE)
            dpts = av_q2d(is->video_st->time_base) * frame->pts;

        // 猜测帧的样本宽高比
        frame->sample_aspect_ratio = av_guess_sample_aspect_ratio(is->ic, is->video_st, frame);

        // 判断是否需要丢帧
        if (framedrop > 0 || (framedrop && get_master_sync_type(is) != AV_SYNC_VIDEO_MASTER)) {
            if (frame->pts != AV_NOPTS_VALUE) { // 如果帧时间戳有效
                double diff = dpts - get_master_clock(is); // 计算与主时钟的时间差
                // 如果时间差在阈值内，并且需要丢帧，则丢弃该帧
                if (!isnan(diff) && fabs(diff) < AV_NOSYNC_THRESHOLD &&
                    diff - is->frame_last_filter_delay < 0 &&
                    is->viddec.pkt_serial == is->vidclk.serial &&
                    is->videoq.nb_packets) {
                    is->frame_drops_early++; // 记录早期丢帧
                    av_frame_unref(frame); // 释放帧的引用
                    got_picture = 0; // 设置为未获取到帧
                }
            }
        }
    }

    return got_picture; // 返回获取帧的状态
}


#if CONFIG_AVFILTER
/* 配置过滤器图，连接源过滤器和接收过滤器 */
static int configure_filtergraph(AVFilterGraph* graph, const char* filtergraph,
    AVFilterContext* source_ctx, AVFilterContext* sink_ctx)
{
    int ret, i; // 定义返回值和循环计数器
    int nb_filters = graph->nb_filters; // 保存图中当前过滤器的数量
    AVFilterInOut* outputs = NULL, * inputs = NULL; // 定义输入和输出连接

    // 如果提供了过滤器图字符串
    if (filtergraph) {
        // 分配输入输出结构体
        outputs = avfilter_inout_alloc();
        inputs = avfilter_inout_alloc();
        if (!outputs || !inputs) { // 检查内存分配是否成功
            ret = AVERROR(ENOMEM); // 失败则设置返回值为内存不足错误
            goto fail; // 跳转到清理部分
        }

        // 设置输出连接的属性
        outputs->name = av_strdup("in"); // 输出名称为 "in"
        outputs->filter_ctx = source_ctx; // 连接到源过滤器
        outputs->pad_idx = 0; // 设置索引为0
        outputs->next = NULL; // 下一连接为空

        // 设置输入连接的属性
        inputs->name = av_strdup("out"); // 输入名称为 "out"
        inputs->filter_ctx = sink_ctx; // 连接到接收过滤器
        inputs->pad_idx = 0; // 设置索引为0
        inputs->next = NULL; // 下一连接为空

        // 解析过滤器图并连接输入输出
        if ((ret = avfilter_graph_parse_ptr(graph, filtergraph, &inputs, &outputs, NULL)) < 0)
            goto fail; // 如果解析失败，跳转到清理部分
    }
    else {
        // 如果未提供过滤器图，直接连接源和接收过滤器
        if ((ret = avfilter_link(source_ctx, 0, sink_ctx, 0)) < 0)
            goto fail; // 如果连接失败，跳转到清理部分
    }

    /* 重新排序过滤器，确保自定义过滤器的输入优先合并 */
    for (i = 0; i < graph->nb_filters - nb_filters; i++)
        FFSWAP(AVFilterContext*, graph->filters[i], graph->filters[i + nb_filters]);

    // 配置过滤器图以完成设置
    ret = avfilter_graph_config(graph, NULL);
fail:
    // 释放分配的输入输出结构
    avfilter_inout_free(&outputs);
    avfilter_inout_free(&inputs);
    return ret; // 返回结果
}


/* 配置视频过滤器图，将视频帧输入并设置过滤器 */
static int configure_video_filters(AVFilterGraph* graph, VideoState* is, const char* vfilters, AVFrame* frame)
{
    // 定义变量和数组
    enum AVPixelFormat pix_fmts[FF_ARRAY_ELEMS(sdl_texture_format_map)]; // 存储支持的像素格式
    char sws_flags_str[512] = ""; // 存储缩放标志的字符串
    char buffersrc_args[256]; // 存储缓冲源过滤器的参数
    int ret; // 存储函数返回值
    AVFilterContext* filt_src = NULL, * filt_out = NULL, * last_filter = NULL; // 过滤器上下文指针
    AVCodecParameters* codecpar = is->video_st->codecpar; // 获取视频流的编解码参数
    AVRational fr = av_guess_frame_rate(is->ic, is->video_st, NULL); // 估计帧率
    const AVDictionaryEntry* e = NULL; // 用于遍历字典
    int nb_pix_fmts = 0; // 当前像素格式数量
    int i, j; // 循环计数器

    // 获取支持的像素格式
    for (i = 0; i < renderer_info.num_texture_formats; i++) {
        for (j = 0; j < FF_ARRAY_ELEMS(sdl_texture_format_map) - 1; j++) {
            if (renderer_info.texture_formats[i] == sdl_texture_format_map[j].texture_fmt) {
                pix_fmts[nb_pix_fmts++] = sdl_texture_format_map[j].format; // 添加像素格式
                break; // 找到匹配的格式后跳出内层循环
            }
        }
    }
    pix_fmts[nb_pix_fmts] = AV_PIX_FMT_NONE; // 结束标记

    // 处理 SWS（缩放）选项
    while ((e = av_dict_iterate(sws_dict, e))) {
        if (!strcmp(e->key, "sws_flags")) {
            av_strlcatf(sws_flags_str, sizeof(sws_flags_str), "%s=%s:", "flags", e->value);
        }
        else {
            av_strlcatf(sws_flags_str, sizeof(sws_flags_str), "%s=%s:", e->key, e->value);
        }
    }
    if (strlen(sws_flags_str)) // 移除最后一个冒号
        sws_flags_str[strlen(sws_flags_str) - 1] = '\0';

    graph->scale_sws_opts = av_strdup(sws_flags_str); // 设置缩放选项

    // 设置缓冲源过滤器的参数
    snprintf(buffersrc_args, sizeof(buffersrc_args),
        "video_size=%dx%d:pix_fmt=%d:time_base=%d/%d:pixel_aspect=%d/%d",
        frame->width, frame->height, frame->format,
        is->video_st->time_base.num, is->video_st->time_base.den,
        codecpar->sample_aspect_ratio.num, FFMAX(codecpar->sample_aspect_ratio.den, 1));
    if (fr.num && fr.den) // 如果帧率有效，添加帧率参数
        av_strlcatf(buffersrc_args, sizeof(buffersrc_args), ":frame_rate=%d/%d", fr.num, fr.den);

    // 创建缓冲源过滤器
    if ((ret = avfilter_graph_create_filter(&filt_src,
        avfilter_get_by_name("buffer"),
        "ffplay_buffer", buffersrc_args, NULL,
        graph)) < 0)
        goto fail; // 创建失败则跳转到清理部分

    // 创建缓冲接收过滤器
    ret = avfilter_graph_create_filter(&filt_out,
        avfilter_get_by_name("buffersink"),
        "ffplay_buffersink", NULL, NULL, graph);
    if (ret < 0)
        goto fail; // 创建失败则跳转到清理部分

    // 设置接收过滤器的像素格式
    if ((ret = av_opt_set_int_list(filt_out, "pix_fmts", pix_fmts, AV_PIX_FMT_NONE, AV_OPT_SEARCH_CHILDREN)) < 0)
        goto fail; // 设置失败则跳转到清理部分

    last_filter = filt_out; // 更新最后一个过滤器指针

    /* 定义宏以在最后添加的过滤器之前插入新过滤器 */
#define INSERT_FILT(name, arg) do {                                          \
    AVFilterContext *filt_ctx;                                               \
                                                                             \
    ret = avfilter_graph_create_filter(&filt_ctx,                            \
                                       avfilter_get_by_name(name),           \
                                       "ffplay_" name, arg, NULL, graph);    \
    if (ret < 0)                                                             \
        goto fail;                                                           \
                                                                             \
    ret = avfilter_link(filt_ctx, 0, last_filter, 0);                       \
    if (ret < 0)                                                             \
        goto fail;                                                           \
                                                                             \
    last_filter = filt_ctx;                                                  \
} while (0)

    // 处理自动旋转
    if (autorotate) {
        double theta = 0.0; // 旋转角度
        int32_t* displaymatrix = NULL; // 显示矩阵
        AVFrameSideData* sd = av_frame_get_side_data(frame, AV_FRAME_DATA_DISPLAYMATRIX);
        if (sd)
            displaymatrix = (int32_t*)sd->data; // 获取显示矩阵数据
        if (!displaymatrix)
            displaymatrix = (int32_t*)av_stream_get_side_data(is->video_st, AV_PKT_DATA_DISPLAYMATRIX, NULL); // 从流中获取数据
        theta = get_rotation(displaymatrix); // 计算旋转角度

        // 根据旋转角度插入相应的过滤器
        if (fabs(theta - 90) < 1.0) {
            INSERT_FILT("transpose", "clock"); // 顺时针旋转90度
        }
        else if (fabs(theta - 180) < 1.0) {
            INSERT_FILT("hflip", NULL); // 水平翻转
            INSERT_FILT("vflip", NULL); // 垂直翻转
        }
        else if (fabs(theta - 270) < 1.0) {
            INSERT_FILT("transpose", "cclock"); // 逆时针旋转90度
        }
        else if (fabs(theta) > 1.0) {
            char rotate_buf[64];
            snprintf(rotate_buf, sizeof(rotate_buf), "%f*PI/180", theta); // 转换为弧度
            INSERT_FILT("rotate", rotate_buf); // 旋转
        }
    }

    // 配置过滤器图并检查返回值
    if ((ret = configure_filtergraph(graph, vfilters, filt_src, last_filter)) < 0)
        goto fail; // 配置失败则跳转到清理部分

    // 保存输入和输出过滤器的引用
    is->in_video_filter = filt_src;
    is->out_video_filter = filt_out;

fail:
    return ret; // 返回结果
}


/* 配置音频过滤器，将音频流输入并设置过滤器 */
static int configure_audio_filters(VideoState* is, const char* afilters, int force_output_format)
{
    static const enum AVSampleFormat sample_fmts[] = { AV_SAMPLE_FMT_S16, AV_SAMPLE_FMT_NONE }; // 定义支持的音频样本格式
    int sample_rates[2] = { 0, -1 }; // 存储样本率
    AVFilterContext* filt_asrc = NULL, * filt_asink = NULL; // 输入和输出过滤器上下文指针
    char aresample_swr_opts[512] = ""; // 存储重采样选项
    const AVDictionaryEntry* e = NULL; // 用于遍历字典
    AVBPrint bp; // 用于构建描述字符串
    char asrc_args[256]; // 存储输入过滤器参数
    int ret; // 存储返回值

    // 释放旧的过滤器图并分配新的过滤器图
    avfilter_graph_free(&is->agraph);
    if (!(is->agraph = avfilter_graph_alloc()))
        return AVERROR(ENOMEM); // 内存分配失败

    // 设置过滤器图的线程数
    is->agraph->nb_threads = filter_nbthreads;

    // 初始化字符串构建器
    av_bprint_init(&bp, 0, AV_BPRINT_SIZE_AUTOMATIC);

    // 遍历字典，构建重采样选项字符串
    while ((e = av_dict_iterate(swr_opts, e)))
        av_strlcatf(aresample_swr_opts, sizeof(aresample_swr_opts), "%s=%s:", e->key, e->value);

    // 移除最后一个冒号
    if (strlen(aresample_swr_opts))
        aresample_swr_opts[strlen(aresample_swr_opts) - 1] = '\0';

    // 设置重采样选项
    av_opt_set(is->agraph, "aresample_swr_opts", aresample_swr_opts, 0);

    // 描述音频通道布局并保存到字符串构建器
    av_channel_layout_describe_bprint(&is->audio_filter_src.ch_layout, &bp);

    // 创建输入过滤器的参数字符串
    ret = snprintf(asrc_args, sizeof(asrc_args),
        "sample_rate=%d:sample_fmt=%s:time_base=%d/%d:channel_layout=%s",
        is->audio_filter_src.freq, av_get_sample_fmt_name(is->audio_filter_src.fmt),
        1, is->audio_filter_src.freq, bp.str);

    // 创建音频缓冲输入过滤器
    ret = avfilter_graph_create_filter(&filt_asrc,
        avfilter_get_by_name("abuffer"), "ffplay_abuffer",
        asrc_args, NULL, is->agraph);
    if (ret < 0)
        goto end; // 创建失败，跳转到清理部分

    // 创建音频缓冲输出过滤器
    ret = avfilter_graph_create_filter(&filt_asink,
        avfilter_get_by_name("abuffersink"), "ffplay_abuffersink",
        NULL, NULL, is->agraph);
    if (ret < 0)
        goto end; // 创建失败，跳转到清理部分

    // 设置输出过滤器的样本格式
    if ((ret = av_opt_set_int_list(filt_asink, "sample_fmts", sample_fmts, AV_SAMPLE_FMT_NONE, AV_OPT_SEARCH_CHILDREN)) < 0)
        goto end; // 设置失败，跳转到清理部分

    // 设置输出过滤器的通道数
    if ((ret = av_opt_set_int(filt_asink, "all_channel_counts", 1, AV_OPT_SEARCH_CHILDREN)) < 0)
        goto end; // 设置失败，跳转到清理部分

    // 如果强制输出格式，配置相关参数
    if (force_output_format) {
        sample_rates[0] = is->audio_tgt.freq; // 设置目标频率
        if ((ret = av_opt_set_int(filt_asink, "all_channel_counts", 0, AV_OPT_SEARCH_CHILDREN)) < 0)
            goto end; // 设置失败，跳转到清理部分
        if ((ret = av_opt_set(filt_asink, "ch_layouts", bp.str, AV_OPT_SEARCH_CHILDREN)) < 0)
            goto end; // 设置失败，跳转到清理部分
        if ((ret = av_opt_set_int_list(filt_asink, "sample_rates", sample_rates, -1, AV_OPT_SEARCH_CHILDREN)) < 0)
            goto end; // 设置失败，跳转到清理部分
    }

    // 配置过滤器图并检查返回值
    if ((ret = configure_filtergraph(is->agraph, afilters, filt_asrc, filt_asink)) < 0)
        goto end; // 配置失败，跳转到清理部分

    // 保存输入和输出过滤器的引用
    is->in_audio_filter = filt_asrc;
    is->out_audio_filter = filt_asink;

end:
    // 如果出错，释放过滤器图
    if (ret < 0)
        avfilter_graph_free(&is->agraph);
    av_bprint_finalize(&bp, NULL); // 清理字符串构建器

    return ret; // 返回结果
}

#endif  /* CONFIG_AVFILTER */


/* 音频处理线程，负责解码音频帧并将其传递给音频过滤器 */
static int audio_thread(void* arg)
{
    VideoState* is = arg; // 将传入的参数转换为 VideoState 指针
    AVFrame* frame = av_frame_alloc(); // 分配音频帧
    Frame* af; // 用于存储输出音频帧
#if CONFIG_AVFILTER
    int last_serial = -1; // 上一个数据包序列号
    int reconfigure; // 标记是否需要重新配置音频过滤器
#endif
    int got_frame = 0; // 是否成功解码帧的标志
    AVRational tb; // 时间基准
    int ret = 0; // 返回值

    // 检查帧分配是否成功
    if (!frame)
        return AVERROR(ENOMEM); // 内存分配失败

    do {
        // 解码音频帧
        if ((got_frame = decoder_decode_frame(&is->auddec, frame, NULL)) < 0)
            goto the_end; // 解码失败，跳转到结束部分

        // 如果成功解码了帧
        if (got_frame) {
            tb = (AVRational){ 1, frame->sample_rate }; // 设置时间基准为样本率的倒数

#if CONFIG_AVFILTER
            // 检查音频格式和参数是否变化，决定是否重新配置过滤器
            reconfigure =
                cmp_audio_fmts(is->audio_filter_src.fmt, is->audio_filter_src.ch_layout.nb_channels,
                    frame->format, frame->ch_layout.nb_channels) ||
                av_channel_layout_compare(&is->audio_filter_src.ch_layout, &frame->ch_layout) ||
                is->audio_filter_src.freq != frame->sample_rate ||
                is->auddec.pkt_serial != last_serial;

            // 如果需要重新配置过滤器
            if (reconfigure) {
                char buf1[1024], buf2[1024]; // 用于描述通道布局的缓冲区
                av_channel_layout_describe(&is->audio_filter_src.ch_layout, buf1, sizeof(buf1));
                av_channel_layout_describe(&frame->ch_layout, buf2, sizeof(buf2));
                av_log(NULL, AV_LOG_DEBUG,
                    "音频帧参数变化：从 rate:%d ch:%d fmt:%s layout:%s serial:%d 到 rate:%d ch:%d fmt:%s layout:%s serial:%d\n",
                    is->audio_filter_src.freq, is->audio_filter_src.ch_layout.nb_channels, av_get_sample_fmt_name(is->audio_filter_src.fmt), buf1, last_serial,
                    frame->sample_rate, frame->ch_layout.nb_channels, av_get_sample_fmt_name(frame->format), buf2, is->auddec.pkt_serial);

                // 更新音频过滤器源的格式和参数
                is->audio_filter_src.fmt = frame->format;
                ret = av_channel_layout_copy(&is->audio_filter_src.ch_layout, &frame->ch_layout);
                if (ret < 0)
                    goto the_end; // 复制失败，跳转到结束部分
                is->audio_filter_src.freq = frame->sample_rate;
                last_serial = is->auddec.pkt_serial; // 更新序列号

                // 配置音频过滤器
                if ((ret = configure_audio_filters(is, afilters, 1)) < 0)
                    goto the_end; // 配置失败，跳转到结束部分
    }

            // 将帧添加到输入过滤器
            if ((ret = av_buffersrc_add_frame(is->in_audio_filter, frame)) < 0)
                goto the_end; // 添加失败，跳转到结束部分

            // 从输出过滤器获取处理后的音频帧
            while ((ret = av_buffersink_get_frame_flags(is->out_audio_filter, frame, 0)) >= 0) {
                tb = av_buffersink_get_time_base(is->out_audio_filter); // 更新时间基准
#endif

                // 获取一个可写的输出帧
                if (!(af = frame_queue_peek_writable(&is->sampq)))
                    goto the_end; // 没有可写的帧，跳转到结束部分

                // 设置输出帧的时间戳和其他参数
                af->pts = (frame->pts == AV_NOPTS_VALUE) ? NAN : frame->pts * av_q2d(tb);
                af->pos = frame->pkt_pos;
                af->serial = is->auddec.pkt_serial;
                af->duration = av_q2d((AVRational) { frame->nb_samples, frame->sample_rate });

                // 移动解码帧的数据到输出帧
                av_frame_move_ref(af->frame, frame);
                frame_queue_push(&is->sampq); // 将输出帧推入帧队列

#if CONFIG_AVFILTER
                // 检查音频队列的序列号
                if (is->audioq.serial != is->auddec.pkt_serial)
                    break; // 如果序列号不同，退出循环
            }
            // 如果到达输入结束，标记解码器为完成
            if (ret == AVERROR_EOF)
                is->auddec.finished = is->auddec.pkt_serial;
#endif
}
    } while (ret >= 0 || ret == AVERROR(EAGAIN) || ret == AVERROR_EOF); // 继续循环，直到没有更多帧

the_end:
#if CONFIG_AVFILTER
    avfilter_graph_free(&is->agraph); // 释放过滤器图
#endif
    av_frame_free(&frame); // 释放帧
    return ret; // 返回结果
}


/* 启动解码器线程 */
static int decoder_start(Decoder* d, int (*fn)(void*), const char* thread_name, void* arg)
{
    // 初始化解码器的包队列
    packet_queue_start(d->queue);

    // 创建一个新的线程，执行传入的解码函数 fn
    d->decoder_tid = SDL_CreateThread(fn, thread_name, arg);

    // 检查线程是否成功创建
    if (!d->decoder_tid) {
        av_log(NULL, AV_LOG_ERROR, "SDL_CreateThread(): %s\n", SDL_GetError()); // 记录错误日志
        return AVERROR(ENOMEM); // 返回内存不足的错误代码
    }

    return 0; // 成功创建线程，返回 0
}

//用于从视频解码器获取视频帧，并通过可选的过滤器处理后将帧推送到显示队列中。
static int video_thread(void* arg)
{
    VideoState* is = arg; // 将传入的参数转换为 VideoState 指针
    AVFrame* frame = av_frame_alloc(); // 分配一个 AVFrame 用于存放视频帧
    double pts; // 存储当前帧的显示时间戳
    double duration; // 存储当前帧的持续时间
    int ret; // 存储函数返回值
    AVRational tb = is->video_st->time_base; // 获取视频流的时间基准
    AVRational frame_rate = av_guess_frame_rate(is->ic, is->video_st, NULL); // 猜测帧率

#if CONFIG_AVFILTER
    AVFilterGraph* graph = NULL; // 过滤器图
    AVFilterContext* filt_out = NULL, * filt_in = NULL; // 输入和输出过滤器上下文
    int last_w = 0; // 存储上一个帧宽度
    int last_h = 0; // 存储上一个帧高度
    enum AVPixelFormat last_format = -2; // 存储上一个帧格式
    int last_serial = -1; // 存储上一个包序列号
    int last_vfilter_idx = 0; // 存储上一个视频过滤器索引
#endif

    if (!frame) // 检查是否成功分配帧
        return AVERROR(ENOMEM); // 返回内存不足的错误代码

    for (;;) { // 无限循环
        ret = get_video_frame(is, frame); // 获取视频帧
        if (ret < 0) // 检查获取帧是否出错
            goto the_end; // 跳转到结束处理
        if (!ret) // 如果没有帧被获取
            continue; // 继续循环

#if CONFIG_AVFILTER
        // 检查视频帧的变化（宽、高、格式、序列号和过滤器索引）
        if (last_w != frame->width
            || last_h != frame->height
            || last_format != frame->format
            || last_serial != is->viddec.pkt_serial
            || last_vfilter_idx != is->vfilter_idx) {
            av_log(NULL, AV_LOG_DEBUG,
                "Video frame changed from size:%dx%d format:%s serial:%d to size:%dx%d format:%s serial:%d\n",
                last_w, last_h,
                (const char*)av_x_if_null(av_get_pix_fmt_name(last_format), "none"), last_serial,
                frame->width, frame->height,
                (const char*)av_x_if_null(av_get_pix_fmt_name(frame->format), "none"), is->viddec.pkt_serial);

            avfilter_graph_free(&graph); // 释放上一个过滤器图
            graph = avfilter_graph_alloc(); // 分配新的过滤器图
            if (!graph) { // 检查分配是否成功
                ret = AVERROR(ENOMEM); // 返回内存不足的错误代码
                goto the_end; // 跳转到结束处理
            }
            graph->nb_threads = filter_nbthreads; // 设置过滤器图的线程数

            // 配置视频过滤器，若失败则推送退出事件
            if ((ret = configure_video_filters(graph, is, vfilters_list ? vfilters_list[is->vfilter_idx] : NULL, frame)) < 0) {
                SDL_Event event;
                event.type = FF_QUIT_EVENT; // 设定事件类型为退出
                event.user.data1 = is; // 将视频状态作为事件数据
                SDL_PushEvent(&event); // 推送事件
                goto the_end; // 跳转到结束处理
            }
            filt_in = is->in_video_filter; // 更新输入过滤器
            filt_out = is->out_video_filter; // 更新输出过滤器
            last_w = frame->width; // 更新最后的宽度
            last_h = frame->height; // 更新最后的高度
            last_format = frame->format; // 更新最后的格式
            last_serial = is->viddec.pkt_serial; // 更新最后的序列号
            last_vfilter_idx = is->vfilter_idx; // 更新最后的过滤器索引
            frame_rate = av_buffersink_get_frame_rate(filt_out); // 获取输出过滤器的帧率
        }

        // 将当前帧添加到输入过滤器中
        ret = av_buffersrc_add_frame(filt_in, frame);
        if (ret < 0) // 检查添加帧是否出错
            goto the_end; // 跳转到结束处理

        while (ret >= 0) { // 当没有错误时
            is->frame_last_returned_time = av_gettime_relative() / 1000000.0; // 获取当前时间

            ret = av_buffersink_get_frame_flags(filt_out, frame, 0); // 从输出过滤器获取帧
            if (ret < 0) { // 检查获取帧是否出错
                if (ret == AVERROR_EOF) // 如果是到达文件尾
                    is->viddec.finished = is->viddec.pkt_serial; // 更新完成标志
                ret = 0; // 重置返回值
                break; // 跳出循环
            }

            // 计算帧的延迟
            is->frame_last_filter_delay = av_gettime_relative() / 1000000.0 - is->frame_last_returned_time;
            if (fabs(is->frame_last_filter_delay) > AV_NOSYNC_THRESHOLD / 10.0) // 检查延迟是否超出阈值
                is->frame_last_filter_delay = 0; // 重置延迟

            tb = av_buffersink_get_time_base(filt_out); // 获取输出过滤器的时间基准
#endif
            // 计算当前帧的持续时间
            duration = (frame_rate.num && frame_rate.den ? av_q2d((AVRational) { frame_rate.den, frame_rate.num }) : 0);
            pts = (frame->pts == AV_NOPTS_VALUE) ? NAN : frame->pts * av_q2d(tb); // 计算当前帧的时间戳
            ret = queue_picture(is, frame, pts, duration, frame->pkt_pos, is->viddec.pkt_serial); // 将帧加入队列
            av_frame_unref(frame); // 释放当前帧的引用

#if CONFIG_AVFILTER
            if (is->videoq.serial != is->viddec.pkt_serial) // 检查视频队列的序列号
                break; // 如果不同，跳出循环
    }
#endif

        if (ret < 0) // 检查加入队列是否出错
            goto the_end; // 跳转到结束处理
}
the_end:
#if CONFIG_AVFILTER
    avfilter_graph_free(&graph); // 释放过滤器图
#endif
    av_frame_free(&frame); // 释放帧
    return 0; // 返回成功
}

//解码字幕线程，解码字幕并将有效的字幕帧添加到字幕队列中，以便后续显示。
static int subtitle_thread(void* arg)
{
    VideoState* is = arg; // 获取传入的 VideoState 结构体指针
    Frame* sp; // 用于存储字幕帧的指针
    int got_subtitle; // 标志是否成功解码字幕
    double pts; // 用于存储字幕的时间戳

    for (;;) {
        // 从字幕队列中获取一个可写的字幕帧
        if (!(sp = frame_queue_peek_writable(&is->subpq)))
            return 0; // 如果没有可写帧，则退出线程

        // 解码字幕帧
        if ((got_subtitle = decoder_decode_frame(&is->subdec, NULL, &sp->sub)) < 0)
            break; // 解码失败，退出循环

        pts = 0; // 初始化时间戳

        // 如果成功解码并且格式为 0（表示有效的字幕）
        if (got_subtitle && sp->sub.format == 0) {
            if (sp->sub.pts != AV_NOPTS_VALUE) // 如果时间戳有效
                pts = sp->sub.pts / (double)AV_TIME_BASE; // 将时间戳转换为秒
            sp->pts = pts; // 更新帧的时间戳
            sp->serial = is->subdec.pkt_serial; // 更新序列号
            sp->width = is->subdec.avctx->width; // 更新字幕宽度
            sp->height = is->subdec.avctx->height; // 更新字幕高度
            sp->uploaded = 0; // 重置上传标志

            // 将字幕帧推入队列
            frame_queue_push(&is->subpq);
        }
        else if (got_subtitle) {
            avsubtitle_free(&sp->sub); // 释放无效的字幕
        }
    }
    return 0; // 线程结束
}


//将音频样本复制到显示缓冲区，以便在编辑窗口中查看。
static void update_sample_display(VideoState* is, short* samples, int samples_size)
{
    int size, len; // 用于计算剩余样本大小和当前处理的样本长度

    size = samples_size / sizeof(short); // 计算样本数量
    while (size > 0) { // 循环直到所有样本都被处理
        len = SAMPLE_ARRAY_SIZE - is->sample_array_index; // 计算剩余缓冲区空间
        if (len > size) // 如果剩余空间大于待处理样本
            len = size; // 只处理剩余样本

        // 复制样本到显示数组
        memcpy(is->sample_array + is->sample_array_index, samples, len * sizeof(short));
        samples += len; // 移动指针到下一个样本
        is->sample_array_index += len; // 更新显示数组索引

        // 如果索引超过数组大小，重置为 0
        if (is->sample_array_index >= SAMPLE_ARRAY_SIZE)
            is->sample_array_index = 0;
        size -= len; // 减少待处理样本数量
    }
}

//根据音频时钟与主时钟之间的差异来调整所需的音频样本数，以同步音频播放。
static int synchronize_audio(VideoState* is, int nb_samples) {
    int wanted_nb_samples = nb_samples; // 初始化所需样本数为当前样本数

    /* if not master, then we try to remove or add samples to correct the clock */
    if (get_master_sync_type(is) != AV_SYNC_AUDIO_MASTER) { // 如果不是主时钟，则尝试调整音频样本
        double diff, avg_diff; // 差异和平均差异
        int min_nb_samples, max_nb_samples; // 最小和最大样本数

        diff = get_clock(&is->audclk) - get_master_clock(is); // 计算音频时钟与主时钟之间的差异

        if (!isnan(diff) && fabs(diff) < AV_NOSYNC_THRESHOLD) { // 如果差异有效且在可接受范围内
            is->audio_diff_cum = diff + is->audio_diff_avg_coef * is->audio_diff_cum; // 累计差异
            if (is->audio_diff_avg_count < AUDIO_DIFF_AVG_NB) { // 如果测量不足
                /* not enough measures to have a correct estimate */
                is->audio_diff_avg_count++; // 增加测量计数
            }
            else {
                /* estimate the A-V difference */
                avg_diff = is->audio_diff_cum * (1.0 - is->audio_diff_avg_coef); // 计算音频与视频的平均差异

                if (fabs(avg_diff) >= is->audio_diff_threshold) { // 如果平均差异超过阈值
                    wanted_nb_samples = nb_samples + (int)(diff * is->audio_src.freq); // 调整所需样本数
                    min_nb_samples = ((nb_samples * (100 - SAMPLE_CORRECTION_PERCENT_MAX) / 100)); // 计算最小样本数
                    max_nb_samples = ((nb_samples * (100 + SAMPLE_CORRECTION_PERCENT_MAX) / 100)); // 计算最大样本数
                    wanted_nb_samples = av_clip(wanted_nb_samples, min_nb_samples, max_nb_samples); // 限制所需样本数在合理范围内
                }
                av_log(NULL, AV_LOG_TRACE, "diff=%f adiff=%f sample_diff=%d apts=%0.3f %f\n", // 记录调试信息
                    diff, avg_diff, wanted_nb_samples - nb_samples,
                    is->audio_clock, is->audio_diff_threshold);
            }
        }
        else {
            /* too big difference : may be initial PTS errors, so
               reset A-V filter */
            is->audio_diff_avg_count = 0; // 重置测量计数
            is->audio_diff_cum = 0; // 重置累计差异
        }
    }

    return wanted_nb_samples; // 返回调整后的所需样本数
}

//（该函数与解码毫无关系）从音频队列中读取AVFrame，处理重采样，并更新音频时钟以确保音频与视频的同步。
static int audio_decode_frame(VideoState* is) {
    int data_size, resampled_data_size; // 数据大小和重采样数据大小
    av_unused double audio_clock0; // 用于保存上一个音频时钟值
    int wanted_nb_samples; // 所需的音频样本数
    Frame* af; // 当前音频帧

    if (is->paused) // 如果播放器处于暂停状态，返回-1
        return -1;

    do {
#if defined(_WIN32)
        while (frame_queue_nb_remaining(&is->sampq) == 0) { // 当音频样本队列为空时
            if ((av_gettime_relative() - audio_callback_time) > 1000000LL * is->audio_hw_buf_size / is->audio_tgt.bytes_per_sec / 2) // 超过缓冲时间，返回-1
                return -1;
            av_usleep(1000); // 等待1毫秒
        }
#endif
        if (!(af = frame_queue_peek_readable(&is->sampq))) // 获取可读音频帧
            return -1;
        frame_queue_next(&is->sampq); // 移动到下一个可读帧
    } while (af->serial != is->audioq.serial); // 确保序列号匹配

    data_size = av_samples_get_buffer_size(NULL, af->frame->ch_layout.nb_channels, // 获取当前帧的数据大小
        af->frame->nb_samples, af->frame->format, 1);

    wanted_nb_samples = synchronize_audio(is, af->frame->nb_samples); // 调整所需样本数以同步音频

    if (af->frame->format != is->audio_src.fmt || // 检查音频格式、通道布局和采样率是否变化
        av_channel_layout_compare(&af->frame->ch_layout, &is->audio_src.ch_layout) ||
        af->frame->sample_rate != is->audio_src.freq ||
        (wanted_nb_samples != af->frame->nb_samples && !is->swr_ctx)) {
        swr_free(&is->swr_ctx); // 释放重采样上下文
        swr_alloc_set_opts2(&is->swr_ctx, // 配置重采样上下文
            &is->audio_tgt.ch_layout, is->audio_tgt.fmt, is->audio_tgt.freq,
            &af->frame->ch_layout, af->frame->format, af->frame->sample_rate,
            0, NULL);
        if (!is->swr_ctx || swr_init(is->swr_ctx) < 0) { // 初始化失败时返回错误
            av_log(NULL, AV_LOG_ERROR,
                "Cannot create sample rate converter for conversion of %d Hz %s %d channels to %d Hz %s %d channels!\n",
                af->frame->sample_rate, av_get_sample_fmt_name(af->frame->format), af->frame->ch_layout.nb_channels,
                is->audio_tgt.freq, av_get_sample_fmt_name(is->audio_tgt.fmt), is->audio_tgt.ch_layout.nb_channels);
            swr_free(&is->swr_ctx);
            return -1;
        }
        if (av_channel_layout_copy(&is->audio_src.ch_layout, &af->frame->ch_layout) < 0) // 复制通道布局
            return -1;
        is->audio_src.freq = af->frame->sample_rate; // 更新源频率
        is->audio_src.fmt = af->frame->format; // 更新源格式
    }

    if (is->swr_ctx) { // 如果存在重采样上下文
        const uint8_t** in = (const uint8_t**)af->frame->extended_data; // 输入数据
        uint8_t** out = &is->audio_buf1; // 输出缓冲区
        int out_count = (int64_t)wanted_nb_samples * is->audio_tgt.freq / af->frame->sample_rate + 256; // 计算输出样本数
        int out_size = av_samples_get_buffer_size(NULL, is->audio_tgt.ch_layout.nb_channels, out_count, is->audio_tgt.fmt, 0); // 计算输出数据大小
        int len2; // 重采样后的数据长度
        if (out_size < 0) { // 如果获取失败返回错误
            av_log(NULL, AV_LOG_ERROR, "av_samples_get_buffer_size() failed\n");
            return -1;
        }
        if (wanted_nb_samples != af->frame->nb_samples) { // 如果所需样本数与帧样本数不同
            if (swr_set_compensation(is->swr_ctx, (wanted_nb_samples - af->frame->nb_samples) * is->audio_tgt.freq / af->frame->sample_rate,
                wanted_nb_samples * is->audio_tgt.freq / af->frame->sample_rate) < 0) { // 设置补偿
                av_log(NULL, AV_LOG_ERROR, "swr_set_compensation() failed\n");
                return -1;
            }
        }
        av_fast_malloc(&is->audio_buf1, &is->audio_buf1_size, out_size); // 为输出缓冲区分配内存
        if (!is->audio_buf1) // 如果分配失败返回错误
            return AVERROR(ENOMEM);
        len2 = swr_convert(is->swr_ctx, out, out_count, in, af->frame->nb_samples); // 重采样
        if (len2 < 0) { // 如果重采样失败返回错误
            av_log(NULL, AV_LOG_ERROR, "swr_convert() failed\n");
            return -1;
        }
        if (len2 == out_count) { // 如果输出大小与请求大小相同，可能缓冲区太小
            av_log(NULL, AV_LOG_WARNING, "audio buffer is probably too small\n");
            if (swr_init(is->swr_ctx) < 0) // 尝试重新初始化重采样上下文
                swr_free(&is->swr_ctx);
        }
        is->audio_buf = is->audio_buf1; // 设置音频缓冲区
        resampled_data_size = len2 * is->audio_tgt.ch_layout.nb_channels * av_get_bytes_per_sample(is->audio_tgt.fmt); // 计算重采样数据大小
    }
    else {
        is->audio_buf = af->frame->data[0]; // 使用原始音频数据
        resampled_data_size = data_size; // 设置重采样数据大小
    }

    audio_clock0 = is->audio_clock; // 保存当前音频时钟值
    /* update the audio clock with the pts */
    if (!isnan(af->pts)) // 如果时间戳有效
        is->audio_clock = af->pts + (double)af->frame->nb_samples / af->frame->sample_rate; // 更新音频时钟
        //此时is->audio_clock就代表该音频被播放完的时间
    else
        is->audio_clock = NAN; // 否则设置为NAN
    is->audio_clock_serial = af->serial; // 更新音频时钟序列号
#ifdef DEBUG
    {
        static double last_clock; // 用于调试的最后时钟值
        printf("audio: delay=%0.3f clock=%0.3f clock0=%0.3f\n", // 输出调试信息
            is->audio_clock - last_clock,
            is->audio_clock, audio_clock0);
        last_clock = is->audio_clock; // 更新最后时钟值
    }
#endif
    return resampled_data_size; // 返回重采样数据大小
    }


//SDL音频回调函数，处理音频输出，将解码的音频数据填充到SDL音频流中，同时负责音频缓冲区的管理和时钟同步。
    static void sdl_audio_callback(void* opaque, Uint8* stream, int len) {
        VideoState* is = opaque; // 将传入的opaque指针转换为VideoState结构体指针
        int audio_size, len1; // 音频数据大小和当前处理长度

        audio_callback_time = av_gettime_relative(); // 获取当前时间，用于同步

        while (len > 0) { // 当还有数据需要处理时
            if (is->audio_buf_index >= is->audio_buf_size) { // 如果当前缓冲区索引大于等于缓冲区大小
                audio_size = audio_decode_frame(is); // 
                if (audio_size < 0) { // 如果解码失败
                    /* if error, just output silence */
                    is->audio_buf = NULL; // 设置音频缓冲区为空
                    // 设置缓冲区大小为最小缓冲区大小
                    is->audio_buf_size = SDL_AUDIO_MIN_BUFFER_SIZE / is->audio_tgt.frame_size * is->audio_tgt.frame_size;
                }
                else { // 解码成功
                    if (is->show_mode != SHOW_MODE_VIDEO) // 如果不是视频显示模式
                        update_sample_display(is, (int16_t*)is->audio_buf, audio_size); // 更新样本显示
                    is->audio_buf_size = audio_size; // 更新音频缓冲区大小
                }
                is->audio_buf_index = 0; // 重置缓冲区索引
            }
            len1 = is->audio_buf_size - is->audio_buf_index; // 计算当前可以处理的长度
            if (len1 > len) // 如果可处理长度大于请求长度
                len1 = len; // 则将其限制为请求长度
            if (!is->muted && is->audio_buf && is->audio_volume == SDL_MIX_MAXVOLUME) // 如果未静音且有音频缓冲
                memcpy(stream, (uint8_t*)is->audio_buf + is->audio_buf_index, len1); // 直接复制音频数据到输出流
            else { // 如果静音或者音量不是最大
                memset(stream, 0, len1); // 输出静音
                if (!is->muted && is->audio_buf) // 如果未静音并且有音频缓冲
                    SDL_MixAudioFormat(stream, (uint8_t*)is->audio_buf + is->audio_buf_index, AUDIO_S16SYS, len1, is->audio_volume); // 混合音频数据
            }
            len -= len1; // 更新剩余处理长度
            stream += len1; // 移动输出流指针
            is->audio_buf_index += len1; // 更新音频缓冲区索引
        }
        is->audio_write_buf_size = is->audio_buf_size - is->audio_buf_index; // 计算写入缓冲区的大小
        /* Let's assume the audio driver that is used by SDL has two periods. */
        if (!isnan(is->audio_clock)) { // 如果音频时钟有效
            set_clock_at(&is->audclk, is->audio_clock - (double)(2 * is->audio_hw_buf_size + is->audio_write_buf_size) / is->audio_tgt.bytes_per_sec, is->audio_clock_serial, audio_callback_time / 1000000.0); // 设置音频时钟
            sync_clock_to_slave(&is->extclk, &is->audclk); // 同步外部时钟
        }
    }

//打开音频设备，设置所需的音频参数（如采样率和频道数），并确保音频格式兼容，返回成功时的缓冲区大小。
    static int audio_open(void* opaque, AVChannelLayout* wanted_channel_layout, int wanted_sample_rate, struct AudioParams* audio_hw_params) {
        SDL_AudioSpec wanted_spec, spec; // 声明所需的音频规格和实际规格
        const char* env; // 环境变量指针
        static const int next_nb_channels[] = { 0, 0, 1, 6, 2, 6, 4, 6 }; // 可能的频道数数组
        static const int next_sample_rates[] = { 0, 44100, 48000, 96000, 192000 }; // 可能的采样率数组
        int next_sample_rate_idx = FF_ARRAY_ELEMS(next_sample_rates) - 1; // 初始化采样率索引
        int wanted_nb_channels = wanted_channel_layout->nb_channels; // 目标频道数

        env = SDL_getenv("SDL_AUDIO_CHANNELS"); // 获取环境变量中设置的频道数
        if (env) { // 如果存在环境变量
            wanted_nb_channels = atoi(env); // 将其转换为整数
            av_channel_layout_uninit(wanted_channel_layout); // 释放旧的频道布局
            av_channel_layout_default(wanted_channel_layout, wanted_nb_channels); // 设置默认频道布局
        }
        if (wanted_channel_layout->order != AV_CHANNEL_ORDER_NATIVE) { // 如果频道布局不是本地顺序
            av_channel_layout_uninit(wanted_channel_layout); // 释放旧的频道布局
            av_channel_layout_default(wanted_channel_layout, wanted_nb_channels); // 设置默认频道布局
        }
        wanted_nb_channels = wanted_channel_layout->nb_channels; // 更新频道数
        wanted_spec.channels = wanted_nb_channels; // 设置目标音频规格的频道数
        wanted_spec.freq = wanted_sample_rate; // 设置目标音频规格的采样率
        if (wanted_spec.freq <= 0 || wanted_spec.channels <= 0) { // 检查采样率和频道数的有效性
            av_log(NULL, AV_LOG_ERROR, "Invalid sample rate or channel count!\n");
            return -1; // 返回错误
        }
        while (next_sample_rate_idx && next_sample_rates[next_sample_rate_idx] >= wanted_spec.freq) // 选择合适的采样率
            next_sample_rate_idx--;
        wanted_spec.format = AUDIO_S16SYS; // 设置音频格式
        wanted_spec.silence = 0; // 设置静音值
        wanted_spec.samples = FFMAX(SDL_AUDIO_MIN_BUFFER_SIZE, 2 << av_log2(wanted_spec.freq / SDL_AUDIO_MAX_CALLBACKS_PER_SEC)); // 设置样本数
        wanted_spec.callback = sdl_audio_callback; // 设置回调函数
        wanted_spec.userdata = opaque; // 设置用户数据

        while (!(audio_dev = SDL_OpenAudioDevice(NULL, 0, &wanted_spec, &spec, SDL_AUDIO_ALLOW_FREQUENCY_CHANGE | SDL_AUDIO_ALLOW_CHANNELS_CHANGE))) { // 打开音频设备
            av_log(NULL, AV_LOG_WARNING, "SDL_OpenAudio (%d channels, %d Hz): %s\n", wanted_spec.channels, wanted_spec.freq, SDL_GetError()); // 记录警告
            wanted_spec.channels = next_nb_channels[FFMIN(7, wanted_spec.channels)]; // 尝试使用下一个可用频道数
            if (!wanted_spec.channels) { // 如果没有可用频道
                wanted_spec.freq = next_sample_rates[next_sample_rate_idx--]; // 尝试下一个采样率
                wanted_spec.channels = wanted_nb_channels; // 恢复目标频道数
                if (!wanted_spec.freq) { // 如果没有更多组合可试
                    av_log(NULL, AV_LOG_ERROR, "No more combinations to try, audio open failed\n");
                    return -1; // 返回错误
                }
            }
            av_channel_layout_default(wanted_channel_layout, wanted_spec.channels); // 更新频道布局
        }

        if (spec.format != AUDIO_S16SYS) { // 检查返回的音频格式
            av_log(NULL, AV_LOG_ERROR, "SDL advised audio format %d is not supported!\n", spec.format);
            return -1; // 返回错误
        }
        if (spec.channels != wanted_spec.channels) { // 检查返回的频道数
            av_channel_layout_uninit(wanted_channel_layout); // 释放旧的频道布局
            av_channel_layout_default(wanted_channel_layout, spec.channels); // 设置新频道布局
            if (wanted_channel_layout->order != AV_CHANNEL_ORDER_NATIVE) { // 如果频道布局不是本地顺序
                av_log(NULL, AV_LOG_ERROR, "SDL advised channel count %d is not supported!\n", spec.channels);
                return -1; // 返回错误
            }
        }

        audio_hw_params->fmt = AV_SAMPLE_FMT_S16; // 设置音频参数格式
        audio_hw_params->freq = spec.freq; // 设置音频参数采样率
        if (av_channel_layout_copy(&audio_hw_params->ch_layout, wanted_channel_layout) < 0) // 复制频道布局
            return -1; // 返回错误
        audio_hw_params->frame_size = av_samples_get_buffer_size(NULL, audio_hw_params->ch_layout.nb_channels, 1, audio_hw_params->fmt, 1); // 计算帧大小
        audio_hw_params->bytes_per_sec = av_samples_get_buffer_size(NULL, audio_hw_params->ch_layout.nb_channels, audio_hw_params->freq, audio_hw_params->fmt, 1); // 计算每秒字节数
        if (audio_hw_params->bytes_per_sec <= 0 || audio_hw_params->frame_size <= 0) { // 检查计算结果
            av_log(NULL, AV_LOG_ERROR, "av_samples_get_buffer_size failed\n");
            return -1; // 返回错误
        }
        return spec.size; // 返回成功时的缓冲区大小
    }

//打开指定流的解码器，配置其参数，初始化相关解码器并处理音频、视频或字幕流，确保流的正确解码和播放。
static int stream_component_open(VideoState *is, int stream_index) {
    AVFormatContext *ic = is->ic; // 获取格式上下文
    AVCodecContext *avctx; // 声明解码器上下文
    const AVCodec *codec; // 声明解码器
    const char *forced_codec_name = NULL; // 强制的解码器名称
    AVDictionary *opts = NULL; // 字典选项
    const AVDictionaryEntry *t = NULL; // 字典条目
    int sample_rate; // 采样率
    AVChannelLayout ch_layout = { 0 }; // 声道布局
    int ret = 0; // 返回值
    int stream_lowres = lowres; // 流的低分辨率设置

    if (stream_index < 0 || stream_index >= ic->nb_streams) // 检查流索引有效性
        return -1;

    avctx = avcodec_alloc_context3(NULL); // 分配解码器上下文
    if (!avctx)
        return AVERROR(ENOMEM); // 内存分配失败

    ret = avcodec_parameters_to_context(avctx, ic->streams[stream_index]->codecpar); // 设置解码器参数
    if (ret < 0)
        goto fail;
    avctx->pkt_timebase = ic->streams[stream_index]->time_base; // 设置时间基

    codec = avcodec_find_decoder(avctx->codec_id); // 查找解码器

    // 根据媒体类型更新流信息
    switch(avctx->codec_type) {
        case AVMEDIA_TYPE_AUDIO:   is->last_audio_stream = stream_index; forced_codec_name = audio_codec_name; break;
        case AVMEDIA_TYPE_SUBTITLE: is->last_subtitle_stream = stream_index; forced_codec_name = subtitle_codec_name; break;
        case AVMEDIA_TYPE_VIDEO:   is->last_video_stream = stream_index; forced_codec_name = video_codec_name; break;
    }

    // 强制使用特定解码器
    if (forced_codec_name)
        codec = avcodec_find_decoder_by_name(forced_codec_name);
    
    // 如果没有找到解码器，返回错误
    if (!codec) {
        if (forced_codec_name) av_log(NULL, AV_LOG_WARNING, "No codec could be found with name '%s'\n", forced_codec_name);
        else av_log(NULL, AV_LOG_WARNING, "No decoder could be found for codec %s\n", avcodec_get_name(avctx->codec_id));
        ret = AVERROR(EINVAL);
        goto fail;
    }

    avctx->codec_id = codec->id; // 设置解码器ID
    if (stream_lowres > codec->max_lowres) { // 检查低分辨率限制
        av_log(avctx, AV_LOG_WARNING, "The maximum value for lowres supported by the decoder is %d\n", codec->max_lowres);
        stream_lowres = codec->max_lowres; // 调整为最大值
    }
    avctx->lowres = stream_lowres; // 设置低分辨率

    if (fast) // 如果设置为快速模式
        avctx->flags2 |= AV_CODEC_FLAG2_FAST; // 设置标志

    // 配置解码器选项
    opts = filter_codec_opts(codec_opts, avctx->codec_id, ic, ic->streams[stream_index], codec);
    if (!av_dict_get(opts, "threads", NULL, 0))
        av_dict_set(&opts, "threads", "auto", 0); // 自动设置线程
    if (stream_lowres)
        av_dict_set_int(&opts, "lowres", stream_lowres, 0); // 设置低分辨率选项

    // 打开解码器
    if ((ret = avcodec_open2(avctx, codec, &opts)) < 0) {
        goto fail; // 打开失败
    }

    // 检查选项字典
    if ((t = av_dict_get(opts, "", NULL, AV_DICT_IGNORE_SUFFIX))) {
        av_log(NULL, AV_LOG_ERROR, "Option %s not found.\n", t->key);
        ret = AVERROR_OPTION_NOT_FOUND;
        goto fail;
    }

    is->eof = 0; // 设置EOF标志
    ic->streams[stream_index]->discard = AVDISCARD_DEFAULT; // 设置丢弃策略

    // 根据媒体类型初始化流
    switch (avctx->codec_type) {
        case AVMEDIA_TYPE_AUDIO: 
#if CONFIG_AVFILTER//音频使用滤镜则进入下面分支，重点是configure_audio_filters函数会配置好入口和出口滤镜
            {
                AVFilterContext *sink;

                is->audio_filter_src.freq = avctx->sample_rate; // 设置频率
                ret = av_channel_layout_copy(&is->audio_filter_src.ch_layout, &avctx->ch_layout); // 复制声道布局
                if (ret < 0)
                    goto fail;
                is->audio_filter_src.fmt = avctx->sample_fmt; // 设置格式
                if ((ret = configure_audio_filters(is, afilters, 0)) < 0)
                    goto fail;
                sink = is->out_audio_filter;
                sample_rate = av_buffersink_get_sample_rate(sink); // 获取输出缓冲区的采样率
                ret = av_buffersink_get_ch_layout(sink, &ch_layout); // 获取声道布局
                if (ret < 0)
                    goto fail;
            }
#else
            sample_rate = avctx->sample_rate; // 设置采样率
            ret = av_channel_layout_copy(&ch_layout, &avctx->ch_layout); // 复制声道布局
            if (ret < 0)
                goto fail;
#endif

            //打开音频设备，设置所需的音频参数（如采样率和频道数），并确保音频格式兼容，返回成功时的缓冲区大小。
            if ((ret = audio_open(is, &ch_layout, sample_rate, &is->audio_tgt)) < 0)
                goto fail;
            is->audio_hw_buf_size = ret; // 设置音频缓冲区大小
            is->audio_src = is->audio_tgt; // 设定源音频参数
            is->audio_buf_size = 0; // 初始化音频缓冲区大小
            is->audio_buf_index = 0; // 初始化缓冲区索引

     ///////////////////////////// 以下这三行变量是用在 音频向视频同步的场景上的，非常难懂，而且应用场景极少。通常音视频同步都是以音频时钟为准
            is->audio_diff_avg_coef = exp(log(0.01) / AUDIO_DIFF_AVG_NB); // 设置平均系数
            is->audio_diff_avg_count = 0; // 初始化计数
            is->audio_diff_threshold = (double)(is->audio_hw_buf_size) / is->audio_tgt.bytes_per_sec; // 设置同步阈值


            //下面是音频解码的重点
            is->audio_stream = stream_index; // 设定音频流索引
            is->audio_st = ic->streams[stream_index]; // 设定音频流

            // 初始化解码器
            if ((ret = decoder_init(&is->auddec, avctx, &is->audioq, is->continue_read_thread)) < 0)
                goto fail;
            if ((is->ic->iformat->flags & (AVFMT_NOBINSEARCH | AVFMT_NOGENSEARCH | AVFMT_NO_BYTE_SEEK)) && !is->ic->iformat->read_seek) {
                is->auddec.start_pts = is->audio_st->start_time; // 设置起始时间戳
                is->auddec.start_pts_tb = is->audio_st->time_base; // 设置时间基
            }
            if ((ret = decoder_start(&is->auddec, audio_thread, "audio_decoder", is)) < 0)//启动音频解码线程
                goto out;
            SDL_PauseAudioDevice(audio_dev, 0); // 开启音频设备
            break;
        case AVMEDIA_TYPE_VIDEO:
            is->video_stream = stream_index; // 设置视频流索引
            is->video_st = ic->streams[stream_index]; // 设置视频流

            // 初始化视频解码器
            if ((ret = decoder_init(&is->viddec, avctx, &is->videoq, is->continue_read_thread)) < 0)
                goto fail;
            if ((ret = decoder_start(&is->viddec, video_thread, "video_decoder", is)) < 0)//启动视频解码线程
                goto out;
            is->queue_attachments_req = 1; // 请求附件
            break;
        case AVMEDIA_TYPE_SUBTITLE:
            is->subtitle_stream = stream_index; // 设置字幕流索引
            is->subtitle_st = ic->streams[stream_index]; // 设置字幕流

            // 初始化字幕解码器
            if ((ret = decoder_init(&is->subdec, avctx, &is->subtitleq, is->continue_read_thread)) < 0)
                goto fail;
            if ((ret = decoder_start(&is->subdec, subtitle_thread, "subtitle_decoder", is)) < 0)//启动字幕解码线程
                goto out;
            break;
        default:
            break; // 其他类型不处理
    }
    goto out;

fail:
    avcodec_free_context(&avctx); // 释放解码器上下文
out:
    av_channel_layout_uninit(&ch_layout); // 释放声道布局
    av_dict_free(&opts); // 释放选项字典

    return ret; // 返回结果
}

//检查是否有解码中止请求。
static int decode_interrupt_cb(void* ctx) {
    VideoState* is = ctx; // 将上下文转换为 VideoState 类型
    return is->abort_request; // 返回中止请求的状态
}

//判断流中是否有足够的数据包以进行解码。
static int stream_has_enough_packets(AVStream* st, int stream_id, PacketQueue* queue) {
    // 检查是否有足够的数据包进行解码
    return stream_id < 0 || // 如果流ID无效
        queue->abort_request || // 如果请求中止
        (st->disposition & AV_DISPOSITION_ATTACHED_PIC) || // 如果流中有附加的图片
        queue->nb_packets > MIN_FRAMES && // 如果队列中的包数量超过最小帧数
        (!queue->duration || av_q2d(st->time_base) * queue->duration > 1.0); // 如果队列持续时间有效并超过阈值
}

//检查给定的格式上下文是否为实时流
static int is_realtime(AVFormatContext* s) {
    // 检查格式上下文是否为实时流
    if (!strcmp(s->iformat->name, "rtp") || // 检查输入格式名称是否为 "rtp"
        !strcmp(s->iformat->name, "rtsp") || // 检查输入格式名称是否为 "rtsp"
        !strcmp(s->iformat->name, "sdp")) // 检查输入格式名称是否为 "sdp"
        return 1; // 如果是实时格式，返回 1

    // 检查 URL 前缀是否为 "rtp:" 或 "udp:"
    if (s->pb &&
        (!strncmp(s->url, "rtp:", 4) || // URL 前缀为 "rtp:"
            !strncmp(s->url, "udp:", 4))) // URL 前缀为 "udp:"
        return 1; // 返回 1 表示为实时流

    return 0; // 否则返回 0
}


//解封装线程，启动音解码线程和视频解码线程，处理seek操作，并读取数据包加入到对应的音视频队列中
static int read_thread(void* arg) {
    VideoState* is = arg; // 将参数转换为 VideoState 类型
    AVFormatContext* ic = NULL; // 初始化格式上下文
    int err, i, ret; // 声明错误、循环变量和返回值
    int st_index[AVMEDIA_TYPE_NB]; // 存储各类型流的索引
    AVPacket* pkt = NULL; // 数据包指针
    int64_t stream_start_time; // 流的起始时间
    int pkt_in_play_range = 0; // 数据包是否在播放范围内
    const AVDictionaryEntry* t; // 字典条目指针
    SDL_mutex* wait_mutex = SDL_CreateMutex(); // 创建互斥锁
    int scan_all_pmts_set = 0; // 标志是否设置了扫描所有 PMT
    int64_t pkt_ts; // 数据包时间戳

    if (!wait_mutex) { // 检查互斥锁是否创建成功
        av_log(NULL, AV_LOG_FATAL, "SDL_CreateMutex(): %s\n", SDL_GetError());
        ret = AVERROR(ENOMEM);
        goto fail;
    }

    memset(st_index, -1, sizeof(st_index)); // 初始化流索引数组为 -1
    is->eof = 0; // 设置文件结束标志为 0

    pkt = av_packet_alloc(); // 分配数据包
    if (!pkt) { // 检查数据包分配是否成功
        av_log(NULL, AV_LOG_FATAL, "Could not allocate packet.\n");
        ret = AVERROR(ENOMEM);
        goto fail;
    }

    ic = avformat_alloc_context(); // 分配格式上下文
    if (!ic) { // 检查上下文分配是否成功
        av_log(NULL, AV_LOG_FATAL, "Could not allocate context.\n");
        ret = AVERROR(ENOMEM);
        goto fail;
    }

    ic->interrupt_callback.callback = decode_interrupt_cb; // 设置中断回调
    ic->interrupt_callback.opaque = is; // 设置上下文

    // 设置扫描所有 PMT 的选项
    if (!av_dict_get(format_opts, "scan_all_pmts", NULL, AV_DICT_MATCH_CASE)) {
        av_dict_set(&format_opts, "scan_all_pmts", "1", AV_DICT_DONT_OVERWRITE);
        scan_all_pmts_set = 1; // 标记已设置
    }

    // 打开输入文件
    err = avformat_open_input(&ic, is->filename, is->iformat, &format_opts);
    if (err < 0) {
        print_error(is->filename, err); // 打印错误
        ret = -1;
        goto fail;
    }

    if (scan_all_pmts_set) // 如果扫描设置已被改变
        av_dict_set(&format_opts, "scan_all_pmts", NULL, AV_DICT_MATCH_CASE);

    // 检查选项字典是否有未找到的选项
    if ((t = av_dict_get(format_opts, "", NULL, AV_DICT_IGNORE_SUFFIX))) {
        av_log(NULL, AV_LOG_ERROR, "Option %s not found.\n", t->key);
        ret = AVERROR_OPTION_NOT_FOUND;
        goto fail;
    }
    is->ic = ic; // 将格式上下文保存到 VideoState

    if (genpts) // 如果需要生成时间戳
        ic->flags |= AVFMT_FLAG_GENPTS;

    av_format_inject_global_side_data(ic); // 注入全局侧数据

    // 查找流信息
    if (find_stream_info) {
        AVDictionary** opts = setup_find_stream_info_opts(ic, codec_opts);
        int orig_nb_streams = ic->nb_streams;

        err = avformat_find_stream_info(ic, opts); // 查找流信息

        for (i = 0; i < orig_nb_streams; i++)
            av_dict_free(&opts[i]); // 释放选项字典
        av_freep(&opts);

        if (err < 0) { // 如果查找失败
            av_log(NULL, AV_LOG_WARNING, "%s: could not find codec parameters\n", is->filename);
            ret = -1;
            goto fail;
        }
    }

    if (ic->pb) // 检查是否有播放上下文
        ic->pb->eof_reached = 0; // 标记未到达文件结尾

    // 设置是否按字节寻址
    if (seek_by_bytes < 0)
        seek_by_bytes = !(ic->iformat->flags & AVFMT_NO_BYTE_SEEK) &&
        !!(ic->iformat->flags & AVFMT_TS_DISCONT) &&
        strcmp("ogg", ic->iformat->name);

    // 设置最大帧持续时间
    is->max_frame_duration = (ic->iformat->flags & AVFMT_TS_DISCONT) ? 10.0 : 3600.0;

    // 设置窗口标题
    if (!window_title && (t = av_dict_get(ic->metadata, "title", NULL, 0)))
        window_title = av_asprintf("%s - %s", t->value, input_filename);

    // 执行寻址请求
    if (start_time != AV_NOPTS_VALUE) {
        int64_t timestamp = start_time; // 设置时间戳

        // 添加流的开始时间
        if (ic->start_time != AV_NOPTS_VALUE)
            timestamp += ic->start_time;

        ret = avformat_seek_file(ic, -1, INT64_MIN, timestamp, INT64_MAX, 0); // 执行寻址
        if (ret < 0) {
            av_log(NULL, AV_LOG_WARNING, "%s: could not seek to position %0.3f\n", is->filename, (double)timestamp / AV_TIME_BASE);
        }
    }

    is->realtime = is_realtime(ic); // 检查是否为实时流

    if (show_status)
        av_dump_format(ic, 0, is->filename, 0); // 显示格式信息

    // 查找希望的流
    for (i = 0; i < ic->nb_streams; i++) {
        AVStream* st = ic->streams[i];
        enum AVMediaType type = st->codecpar->codec_type;
        st->discard = AVDISCARD_ALL; // 标记为丢弃流
        if (type >= 0 && wanted_stream_spec[type] && st_index[type] == -1)
            if (avformat_match_stream_specifier(ic, st, wanted_stream_spec[type]) > 0)
                st_index[type] = i; // 保存流索引
    }

    // 检查所有希望的流是否有效
    for (i = 0; i < AVMEDIA_TYPE_NB; i++) {
        if (wanted_stream_spec[i] && st_index[i] == -1) {
            av_log(NULL, AV_LOG_ERROR, "Stream specifier %s does not match any %s stream\n", wanted_stream_spec[i], av_get_media_type_string(i));
            st_index[i] = INT_MAX; // 设置为无效
        }
    }

    // 查找最佳流
    if (!video_disable)
        st_index[AVMEDIA_TYPE_VIDEO] = av_find_best_stream(ic, AVMEDIA_TYPE_VIDEO, st_index[AVMEDIA_TYPE_VIDEO], -1, NULL, 0);
    if (!audio_disable)
        st_index[AVMEDIA_TYPE_AUDIO] = av_find_best_stream(ic, AVMEDIA_TYPE_AUDIO, st_index[AVMEDIA_TYPE_AUDIO], st_index[AVMEDIA_TYPE_VIDEO], NULL, 0);
    if (!video_disable && !subtitle_disable)
        st_index[AVMEDIA_TYPE_SUBTITLE] = av_find_best_stream(ic, AVMEDIA_TYPE_SUBTITLE, st_index[AVMEDIA_TYPE_SUBTITLE], (st_index[AVMEDIA_TYPE_AUDIO] >= 0 ? st_index[AVMEDIA_TYPE_AUDIO] : st_index[AVMEDIA_TYPE_VIDEO]), NULL, 0);

    is->show_mode = show_mode; // 设置显示模式
    if (st_index[AVMEDIA_TYPE_VIDEO] >= 0) {
        AVStream* st = ic->streams[st_index[AVMEDIA_TYPE_VIDEO]];
        AVCodecParameters* codecpar = st->codecpar;
        AVRational sar = av_guess_sample_aspect_ratio(ic, st, NULL); // 估算样本宽高比
        if (codecpar->width)
            set_default_window_size(codecpar->width, codecpar->height, sar); // 设置默认窗口大小
    }

    
    if (st_index[AVMEDIA_TYPE_AUDIO] >= 0) {
        stream_component_open(is, st_index[AVMEDIA_TYPE_AUDIO]);// 打开音频流
    }

    ret = -1; // 初始化返回值为 -1
    if (st_index[AVMEDIA_TYPE_VIDEO] >= 0) {
        ret = stream_component_open(is, st_index[AVMEDIA_TYPE_VIDEO]); // 打开视频流
    }
    if (is->show_mode == SHOW_MODE_NONE) // 如果没有显示模式
        is->show_mode = ret >= 0 ? SHOW_MODE_VIDEO : SHOW_MODE_RDFT; // 根据打开结果设置显示模式

    if (st_index[AVMEDIA_TYPE_SUBTITLE] >= 0) {
        stream_component_open(is, st_index[AVMEDIA_TYPE_SUBTITLE]); // 打开字幕流
    }

    // 检查是否打开了有效的音视频流
    if (is->video_stream < 0 && is->audio_stream < 0) {
        av_log(NULL, AV_LOG_FATAL, "Failed to open file '%s' or configure filtergraph\n", is->filename);
        ret = -1;
        goto fail;
    }

    // 设置无限缓冲标志
    if (infinite_buffer < 0 && is->realtime)
        infinite_buffer = 1;

    for (;;) {
        if (is->abort_request) // 检查是否请求中止
            break;

        // 处理暂停状态
        if (is->paused != is->last_paused) {
            is->last_paused = is->paused;
            if (is->paused)
                is->read_pause_return = av_read_pause(ic);//只对网络流播放有效
            else
                av_read_play(ic);
        }

        // 处理 RTSP 协议的暂停
#if CONFIG_RTSP_DEMUXER || CONFIG_MMSH_PROTOCOL
        if (is->paused && (!strcmp(ic->iformat->name, "rtsp") || (ic->pb && !strncmp(input_filename, "mmsh:", 5)))) {
            SDL_Delay(10); // 等待 10 毫秒
            continue;
        }
#endif

        // 处理寻址请求
        if (is->seek_req) {
            int64_t seek_target = is->seek_pos;
            int64_t seek_min = is->seek_rel > 0 ? seek_target - is->seek_rel + 2 : INT64_MIN;
            int64_t seek_max = is->seek_rel < 0 ? seek_target - is->seek_rel - 2 : INT64_MAX;

            ret = avformat_seek_file(is->ic, -1, seek_min, seek_target, seek_max, is->seek_flags);
            if (ret < 0) {
                av_log(NULL, AV_LOG_ERROR, "%s: error while seeking\n", is->ic->url);
            }
            else {
                // 清空音频、字幕和视频的包队列
                if (is->audio_stream >= 0)
                    packet_queue_flush(&is->audioq);
                if (is->subtitle_stream >= 0)
                    packet_queue_flush(&is->subtitleq);
                if (is->video_stream >= 0)
                    packet_queue_flush(&is->videoq);
                // 设置时钟
                set_clock(&is->extclk, is->seek_flags & AVSEEK_FLAG_BYTE ? NAN : seek_target / (double)AV_TIME_BASE, 0);
            }
            is->seek_req = 0;
            is->queue_attachments_req = 1; // 请求队列附加图像
            is->eof = 0; // 重置文件结束标志
            if (is->paused)
                step_to_next_frame(is); // 步进到下一帧
        }

        // 处理附加图像
        if (is->queue_attachments_req) {
            if (is->video_st && is->video_st->disposition & AV_DISPOSITION_ATTACHED_PIC) {
                if ((ret = av_packet_ref(pkt, &is->video_st->attached_pic)) < 0)
                    goto fail;
                packet_queue_put(&is->videoq, pkt); // 将附加图像放入视频队列
                packet_queue_put_nullpacket(&is->videoq, pkt, is->video_stream); // 发送空数据包
            }
            is->queue_attachments_req = 0;
        }

        // 检查队列是否已满
        if (infinite_buffer < 1 && 
            (is->audioq.size + is->videoq.size + is->subtitleq.size > MAX_QUEUE_SIZE ||
            (stream_has_enough_packets(is->audio_st, is->audio_stream, &is->audioq) &&
                stream_has_enough_packets(is->video_st, is->video_stream, &is->videoq) &&
                stream_has_enough_packets(is->subtitle_st, is->subtitle_stream, &is->subtitleq)))) {
            SDL_LockMutex(wait_mutex); // 锁定互斥锁
            SDL_CondWaitTimeout(is->continue_read_thread, wait_mutex, 10); // 等待信号
            SDL_UnlockMutex(wait_mutex); // 解锁互斥锁
            continue;
        }

        // 检查是否需要循环播放
        if (!is->paused && (!is->audio_st || (is->auddec.finished == is->audioq.serial && frame_queue_nb_remaining(&is->sampq) == 0)) &&
            (!is->video_st || (is->viddec.finished == is->videoq.serial && frame_queue_nb_remaining(&is->pictq) == 0))) {
            if (loop != 1 && (!loop || --loop)) {
                stream_seek(is, start_time != AV_NOPTS_VALUE ? start_time : 0, 0, 0);
            }
            else if (autoexit) {
                ret = AVERROR_EOF;
                goto fail;
            }
        }

        // 读取数据包
        ret = av_read_frame(ic, pkt);
        if (ret < 0) {
            if ((ret == AVERROR_EOF || avio_feof(ic->pb)) && !is->eof) {
                if (is->video_stream >= 0)
                    packet_queue_put_nullpacket(&is->videoq, pkt, is->video_stream);
                if (is->audio_stream >= 0)
                    packet_queue_put_nullpacket(&is->audioq, pkt, is->audio_stream);
                if (is->subtitle_stream >= 0)
                    packet_queue_put_nullpacket(&is->subtitleq, pkt, is->subtitle_stream);
                is->eof = 1; // 设置为已到达文件结束
            }
            if (ic->pb && ic->pb->error) {
                if (autoexit)
                    goto fail; // 如果发生错误且设置了自动退出
                else
                    break; // 退出循环
            }
            SDL_LockMutex(wait_mutex);
            SDL_CondWaitTimeout(is->continue_read_thread, wait_mutex, 10);
            SDL_UnlockMutex(wait_mutex);
            continue;
        }
        else {
            is->eof = 0; // 重置结束标志
        }

        // 检查数据包是否在用户指定的播放范围内
        stream_start_time = ic->streams[pkt->stream_index]->start_time;
        pkt_ts = pkt->pts == AV_NOPTS_VALUE ? pkt->dts : pkt->pts; // 获取时间戳
        pkt_in_play_range = duration == AV_NOPTS_VALUE ||
            (pkt_ts - (stream_start_time != AV_NOPTS_VALUE ? stream_start_time : 0)) *
            av_q2d(ic->streams[pkt->stream_index]->time_base) -
            (double)(start_time != AV_NOPTS_VALUE ? start_time : 0) / 1000000
            <= ((double)duration / 1000000);

        // 将数据包放入相应队列
        if (pkt->stream_index == is->audio_stream && pkt_in_play_range) {
            packet_queue_put(&is->audioq, pkt);
        }
        else if (pkt->stream_index == is->video_stream && pkt_in_play_range && !(is->video_st->disposition & AV_DISPOSITION_ATTACHED_PIC)) {
            packet_queue_put(&is->videoq, pkt);
        }
        else if (pkt->stream_index == is->subtitle_stream && pkt_in_play_range) {
            packet_queue_put(&is->subtitleq, pkt);
        }
        else {
            av_packet_unref(pkt); // 释放未使用的数据包
        }
        }

    ret = 0; // 设置返回值为 0
fail:
    if (ic && !is->ic)
        avformat_close_input(&ic); // 关闭输入文件

    av_packet_free(&pkt); // 释放数据包
    if (ret != 0) {
        SDL_Event event;

        event.type = FF_QUIT_EVENT; // 设置退出事件类型
        event.user.data1 = is; // 传递数据
        SDL_PushEvent(&event); // 推送事件
    }
    SDL_DestroyMutex(wait_mutex); // 销毁互斥锁
    return 0; // 返回
    }

//于初始化视频流的状态，分配必要的资源，并创建用于解复用线程（读取媒体文件的线程read_thread）。
static VideoState *stream_open(const char *filename,
                               const AVInputFormat *iformat)
{
    VideoState *is; // 定义一个指向 VideoState 结构的指针

    is = av_mallocz(sizeof(VideoState)); // 分配并初始化 VideoState 结构
    if (!is) // 检查分配是否成功
        return NULL; // 如果分配失败，返回 NULL

    is->last_video_stream = is->video_stream = -1; // 初始化视频流索引为 -1
    is->last_audio_stream = is->audio_stream = -1; // 初始化音频流索引为 -1
    is->last_subtitle_stream = is->subtitle_stream = -1; // 初始化字幕流索引为 -1
    is->filename = av_strdup(filename); // 复制文件名字符串
    if (!is->filename) // 检查文件名复制是否成功
        goto fail; // 失败则跳转到失败处理部分

    is->iformat = iformat; // 设置输入格式
    is->ytop = 0; // 初始化 y 坐标
    is->xleft = 0; // 初始化 x 坐标

    /* start video display */
    if (frame_queue_init(&is->pictq, &is->videoq, VIDEO_PICTURE_QUEUE_SIZE, 1) < 0) // 初始化视频帧队列
        goto fail; // 失败则跳转到失败处理部分
    if (frame_queue_init(&is->subpq, &is->subtitleq, SUBPICTURE_QUEUE_SIZE, 0) < 0) // 初始化字幕队列
        goto fail; 
    if (frame_queue_init(&is->sampq, &is->audioq, SAMPLE_QUEUE_SIZE, 1) < 0) // 初始化音频样本队列
        goto fail; 

    if (packet_queue_init(&is->videoq) < 0 || // 初始化视频包队列
        packet_queue_init(&is->audioq) < 0 || // 初始化音频包队列
        packet_queue_init(&is->subtitleq) < 0) // 初始化字幕包队列
        goto fail; // 失败则跳转到失败处理部分

    if (!(is->continue_read_thread = SDL_CreateCond())) { // 创建条件变量用于线程同步
        av_log(NULL, AV_LOG_FATAL, "SDL_CreateCond(): %s\n", SDL_GetError()); // 错误日志
        goto fail; // 失败则跳转到失败处理部分
    }

    init_clock(&is->vidclk, &is->videoq.serial); // 初始化视频时钟
    init_clock(&is->audclk, &is->audioq.serial); // 初始化音频时钟
    init_clock(&is->extclk, &is->extclk.serial); // 初始化外部时钟
    is->audio_clock_serial = -1; // 初始化音频时钟序列号为 -1

    if (startup_volume < 0) // 检查初始音量
        av_log(NULL, AV_LOG_WARNING, "-volume=%d < 0, setting to 0\n", startup_volume); // 如果小于 0，记录警告并设置为 0
    if (startup_volume > 100) // 检查初始音量
        av_log(NULL, AV_LOG_WARNING, "-volume=%d > 100, setting to 100\n", startup_volume); // 如果大于 100，记录警告并设置为 100

    startup_volume = av_clip(startup_volume, 0, 100); // 限制音量在 0 到 100 之间
    startup_volume = av_clip(SDL_MIX_MAXVOLUME * startup_volume / 100, 0, SDL_MIX_MAXVOLUME); // 将音量转换为 SDL 所需的范围
    is->audio_volume = startup_volume; // 设置音频音量
    is->muted = 0; // 设置静音状态为 0（未静音）
    is->av_sync_type = av_sync_type; // 设置音视频同步类型为音频时钟

    is->read_tid = SDL_CreateThread(read_thread, "read_thread", is); // 创建解复用线程
    if (!is->read_tid) { // 检查线程是否成功创建
        av_log(NULL, AV_LOG_FATAL, "SDL_CreateThread(): %s\n", SDL_GetError()); // 记录错误
fail:
        stream_close(is); // 关闭流并释放资源
        return NULL; // 返回 NULL 表示失败
    }
    return is; // 返回成功创建的 VideoState 结构指针
}

//用于在视频、音频或字幕流之间切换，确保新流的参数有效并更新相关状态。
static void stream_cycle_channel(VideoState* is, int codec_type)
{
    AVFormatContext* ic = is->ic; // 获取当前格式上下文
    int start_index, stream_index; // 初始化流的起始索引和当前索引
    int old_index; // 记录旧的流索引
    AVStream* st; // 指向当前流
    AVProgram* p = NULL; // 指向程序
    int nb_streams = is->ic->nb_streams; // 获取流的数量

    // 根据 codec_type 设置起始索引和旧索引
    if (codec_type == AVMEDIA_TYPE_VIDEO) {
        start_index = is->last_video_stream; // 获取最后一个视频流的索引
        old_index = is->video_stream; // 获取当前视频流的索引
    }
    else if (codec_type == AVMEDIA_TYPE_AUDIO) {
        start_index = is->last_audio_stream; // 获取最后一个音频流的索引
        old_index = is->audio_stream; // 获取当前音频流的索引
    }
    else {
        start_index = is->last_subtitle_stream; // 获取最后一个字幕流的索引
        old_index = is->subtitle_stream; // 获取当前字幕流的索引
    }

    stream_index = start_index; // 设置当前流索引为起始索引

    // 如果是音频或字幕流，且当前存在视频流
    if (codec_type != AVMEDIA_TYPE_VIDEO && is->video_stream != -1) {
        p = av_find_program_from_stream(ic, NULL, is->video_stream); // 查找视频流对应的程序
        if (p) {
            nb_streams = p->nb_stream_indexes; // 获取该程序的流索引数量
            for (start_index = 0; start_index < nb_streams; start_index++)
                if (p->stream_index[start_index] == stream_index) // 找到当前流索引
                    break; // 找到后跳出循环
            if (start_index == nb_streams) // 如果没有找到
                start_index = -1; // 设置为 -1
            stream_index = start_index; // 更新当前流索引
        }
    }

    for (;;) { // 循环遍历流
        if (++stream_index >= nb_streams) // 如果当前流索引超出范围
        {
            if (codec_type == AVMEDIA_TYPE_SUBTITLE) // 如果是字幕流
            {
                stream_index = -1; // 设置流索引为 -1
                is->last_subtitle_stream = -1; // 更新最后字幕流索引
                goto the_end; // 跳转到结束
            }
            if (start_index == -1) // 如果起始索引为 -1
                return; // 结束函数
            stream_index = 0; // 重置流索引为 0
        }
        if (stream_index == start_index) // 如果流索引回到起始索引
            return; // 结束函数

        st = is->ic->streams[p ? p->stream_index[stream_index] : stream_index]; // 获取当前流
        if (st->codecpar->codec_type == codec_type) { // 如果流的类型匹配
            /* check that parameters are OK */
            switch (codec_type) { // 检查参数
            case AVMEDIA_TYPE_AUDIO:
                if (st->codecpar->sample_rate != 0 && // 如果采样率有效
                    st->codecpar->ch_layout.nb_channels != 0) // 如果通道数有效
                    goto the_end; // 跳转到结束
                break;
            case AVMEDIA_TYPE_VIDEO:
            case AVMEDIA_TYPE_SUBTITLE:
                goto the_end; // 跳转到结束
            default:
                break;
            }
        }
    }
the_end: // 结束部分
    if (p && stream_index != -1) // 如果有程序且流索引有效
        stream_index = p->stream_index[stream_index]; // 更新流索引为程序中的索引

    av_log(NULL, AV_LOG_INFO, "Switch %s stream from #%d to #%d\n", // 记录日志
        av_get_media_type_string(codec_type), // 获取媒体类型字符串
        old_index, // 旧索引
        stream_index); // 新索引

    stream_component_close(is, old_index); // 关闭旧的流组件
    stream_component_open(is, stream_index); // 打开新的流组件
}

//切换全屏状态
static void toggle_full_screen(VideoState* is)
{
    is_full_screen = !is_full_screen; // 切换全屏状态
    SDL_SetWindowFullscreen(window, is_full_screen ? SDL_WINDOW_FULLSCREEN_DESKTOP : 0); // 设置窗口为全屏或窗口模式
}

//切换音频显示模式
static void toggle_audio_display(VideoState* is)
{
    int next = is->show_mode; // 获取当前显示模式
    do {
        next = (next + 1) % SHOW_MODE_NB; // 循环到下一个显示模式
    } while (next != is->show_mode && // 如果新模式与当前模式不同
        (next == SHOW_MODE_VIDEO && !is->video_st || // 视频模式且没有视频流
            next != SHOW_MODE_VIDEO && !is->audio_st)); // 非视频模式且没有音频流
    if (is->show_mode != next) { // 如果显示模式改变
        is->force_refresh = 1; // 强制刷新
        is->show_mode = next; // 更新显示模式
    }
}

//处理事件循环和视频刷新。
static void refresh_loop_wait_event(VideoState* is, SDL_Event* event) {
    double remaining_time = 0.0; // 剩余时间初始化为 0
    SDL_PumpEvents(); // 更新 SDL 事件状态
    while (!SDL_PeepEvents(event, 1, SDL_GETEVENT, SDL_FIRSTEVENT, SDL_LASTEVENT)) { // 检查事件队列是否为空
        if (!cursor_hidden && av_gettime_relative() - cursor_last_shown > CURSOR_HIDE_DELAY) { // 如果光标未隐藏且超过延迟时间
            SDL_ShowCursor(0); // 隐藏光标
            cursor_hidden = 1; // 更新光标状态
        }
        if (remaining_time > 0.0) // 如果还有剩余时间
            av_usleep((int64_t)(remaining_time * 1000000.0)); // 休眠剩余时间
        remaining_time = REFRESH_RATE; // 重置剩余时间为刷新率
        if (is->show_mode != SHOW_MODE_NONE && (!is->paused || is->force_refresh)) // 如果不在暂停状态且需要刷新
            video_refresh(is, &remaining_time); // 刷新视频
        SDL_PumpEvents(); // 继续更新 SDL 事件状态
    }
}

//用于在视频播放中根据增量值跳转到相应的章节。
static void seek_chapter(VideoState* is, int incr)
{
    int64_t pos = get_master_clock(is) * AV_TIME_BASE; // 获取当前播放位置，并转换为时间基准
    int i;

    if (!is->ic->nb_chapters) // 如果没有章节
        return; // 直接返回

    /* find the current chapter */
    for (i = 0; i < is->ic->nb_chapters; i++) { // 遍历所有章节
        AVChapter* ch = is->ic->chapters[i]; // 获取当前章节
        if (av_compare_ts(pos, AV_TIME_BASE_Q, ch->start, ch->time_base) < 0) { // 如果当前播放位置小于章节起始时间
            i--; // 记录当前章节索引
            break; // 退出循环
        }
    }

    i += incr; // 根据增量调整章节索引
    i = FFMAX(i, 0); // 确保章节索引不小于 0
    if (i >= is->ic->nb_chapters) // 如果章节索引超出范围
        return; // 直接返回

    av_log(NULL, AV_LOG_VERBOSE, "Seeking to chapter %d.\n", i); // 打印正在跳转的章节
    stream_seek(is, av_rescale_q(is->ic->chapters[i]->start, is->ic->chapters[i]->time_base,
        AV_TIME_BASE_Q), 0, 0); // 跳转到指定章节的起始位置
}


//负责处理和响应视频播放中的各种用户输入事件，包括按键、鼠标点击和窗口事件，以实现视频的播放控制、跳转、全屏切换等功能。
static void event_loop(VideoState* cur_stream)
{
    SDL_Event event; // 创建SDL事件结构体
    double incr, pos, frac; // 定义增量、位置和分数变量

    for (;;) { // 无限循环，等待事件
        double x;
        refresh_loop_wait_event(cur_stream, &event); // 刷新并等待事件
        switch (event.type) { // 根据事件类型处理
        case SDL_KEYDOWN: // 按键按下事件
            if (exit_on_keydown || event.key.keysym.sym == SDLK_ESCAPE || event.key.keysym.sym == SDLK_q) { // 检查是否退出
                do_exit(cur_stream); // 退出程序
                break;
            }
            // 如果尚未创建窗口，跳过所有按键事件
            if (!cur_stream->width)
                continue; // 继续等待事件

            switch (event.key.keysym.sym) { // 处理不同的按键
            case SDLK_f: // 切换全屏
                toggle_full_screen(cur_stream);
                cur_stream->force_refresh = 1; // 强制刷新
                break;
            case SDLK_p: // 暂停/播放切换
            case SDLK_SPACE:
                toggle_pause(cur_stream);
                break;
            case SDLK_m: // 静音切换
                toggle_mute(cur_stream);
                break;
            case SDLK_KP_MULTIPLY: // 增加音量
            case SDLK_0:
                update_volume(cur_stream, 1, SDL_VOLUME_STEP);
                break;
            case SDLK_KP_DIVIDE: // 减少音量
            case SDLK_9:
                update_volume(cur_stream, -1, SDL_VOLUME_STEP);
                break;
            case SDLK_s: // 单步播放
                step_to_next_frame(cur_stream);
                break;
            case SDLK_a: // 切换音频通道
                stream_cycle_channel(cur_stream, AVMEDIA_TYPE_AUDIO);
                break;
            case SDLK_v: // 切换视频通道
                stream_cycle_channel(cur_stream, AVMEDIA_TYPE_VIDEO);
                break;
            case SDLK_c: // 切换视频、音频和字幕通道
                stream_cycle_channel(cur_stream, AVMEDIA_TYPE_VIDEO);
                stream_cycle_channel(cur_stream, AVMEDIA_TYPE_AUDIO);
                stream_cycle_channel(cur_stream, AVMEDIA_TYPE_SUBTITLE);
                break;
            case SDLK_t: // 切换字幕通道
                stream_cycle_channel(cur_stream, AVMEDIA_TYPE_SUBTITLE);
                break;
            case SDLK_w: // 切换音频显示或视频滤镜
#if CONFIG_AVFILTER
                if (cur_stream->show_mode == SHOW_MODE_VIDEO && cur_stream->vfilter_idx < nb_vfilters - 1) {
                    if (++cur_stream->vfilter_idx >= nb_vfilters)
                        cur_stream->vfilter_idx = 0;
                }
                else {
                    cur_stream->vfilter_idx = 0;
                    toggle_audio_display(cur_stream);
            }
#else
                toggle_audio_display(cur_stream);
#endif
                break;
            case SDLK_PAGEUP: // 切换到下一章节
                if (cur_stream->ic->nb_chapters <= 1) {
                    incr = 600.0; // 定义默认增量
                    goto do_seek; // 跳转到查找位置
                }
                seek_chapter(cur_stream, 1); // 跳转到下一章节
                break;
            case SDLK_PAGEDOWN: // 切换到上一章节
                if (cur_stream->ic->nb_chapters <= 1) {
                    incr = -600.0; // 定义默认增量
                    goto do_seek; // 跳转到查找位置
                }
                seek_chapter(cur_stream, -1); // 跳转到上一章节
                break;
            case SDLK_LEFT: // 向后跳转
                incr = seek_interval ? -seek_interval : -10.0; // 设定增量
                goto do_seek; // 跳转到查找位置
            case SDLK_RIGHT: // 向前跳转
                incr = seek_interval ? seek_interval : 10.0; // 设定增量
                goto do_seek; // 跳转到查找位置
            case SDLK_UP: // 向前跳转60秒
                incr = 60.0; // 设定增量
                goto do_seek; // 跳转到查找位置
            case SDLK_DOWN: // 向后跳转60秒
                incr = -60.0; // 设定增量
            do_seek: // 查找位置
                if (seek_by_bytes) { // 按字节跳转
                    pos = -1; // 初始化位置为-1
                    if (pos < 0 && cur_stream->video_stream >= 0) // 如果没有位置且有视频流
                        pos = frame_queue_last_pos(&cur_stream->pictq); // 获取视频队列最后的位置
                    if (pos < 0 && cur_stream->audio_stream >= 0) // 如果没有位置且有音频流
                        pos = frame_queue_last_pos(&cur_stream->sampq); // 获取音频队列最后的位置
                    if (pos < 0)
                        pos = avio_tell(cur_stream->ic->pb); // 获取当前字节位置
                    if (cur_stream->ic->bit_rate)
                        incr *= cur_stream->ic->bit_rate / 8.0; // 计算字节增量
                    else
                        incr *= 180000.0; // 设置默认字节增量
                    pos += incr; // 更新位置
                    stream_seek(cur_stream, pos, incr, 1); // 执行跳转
                }
                else { // 按时间跳转
                    pos = get_master_clock(cur_stream); // 获取当前时间
                    if (isnan(pos))
                        pos = (double)cur_stream->seek_pos / AV_TIME_BASE; // 获取回调位置
                    pos += incr; // 更新位置
                    if (cur_stream->ic->start_time != AV_NOPTS_VALUE && pos < cur_stream->ic->start_time / (double)AV_TIME_BASE)
                        pos = cur_stream->ic->start_time / (double)AV_TIME_BASE; // 确保位置不小于起始时间
                    stream_seek(cur_stream, (int64_t)(pos * AV_TIME_BASE), (int64_t)(incr * AV_TIME_BASE), 0); // 执行时间跳转
                }
                break;
            default: // 其他按键事件
                break;
        }
            break;
        case SDL_MOUSEBUTTONDOWN: // 鼠标按钮按下事件
            if (exit_on_mousedown) { // 检查是否退出
                do_exit(cur_stream); // 退出程序
                break;
            }
            if (event.button.button == SDL_BUTTON_LEFT) { // 左键点击事件
                static int64_t last_mouse_left_click = 0; // 记录上次左键点击时间
                if (av_gettime_relative() - last_mouse_left_click <= 500000) { // 双击检测
                    toggle_full_screen(cur_stream); // 切换全屏
                    cur_stream->force_refresh = 1; // 强制刷新
                    last_mouse_left_click = 0; // 重置点击时间
                }
                else {
                    last_mouse_left_click = av_gettime_relative(); // 更新点击时间
                }
            }
        case SDL_MOUSEMOTION: // 鼠标移动事件
            if (cursor_hidden) { // 如果光标隐藏
                SDL_ShowCursor(1); // 显示光标
                cursor_hidden = 0; // 更新光标状态
            }
            cursor_last_shown = av_gettime_relative(); // 更新光标最后显示时间
            if (event.type == SDL_MOUSEBUTTONDOWN) { // 检查是否为鼠标按钮事件
                if (event.button.button != SDL_BUTTON_RIGHT) // 如果不是右键点击
                    break; // 跳过
                x = event.button.x; // 获取点击位置
            }
            else { // 如果是鼠标移动事件
                if (!(event.motion.state & SDL_BUTTON_RMASK)) // 检查右键是否按下
                    break; // 跳过
                x = event.motion.x; // 获取当前位置
            }
            if (seek_by_bytes || cur_stream->ic->duration <= 0) { // 如果按字节跳转或没有持续时间
                uint64_t size = avio_size(cur_stream->ic->pb); // 获取总字节数
                stream_seek(cur_stream, size * x / cur_stream->width, 0, 1); // 根据点击位置进行字节跳转
            }
            else { // 按时间跳转
                int64_t ts;
                int ns, hh, mm, ss; // 定义时间变量
                int tns, thh, tmm, tss; // 定义总时间变量
                tns = cur_stream->ic->duration / 1000000LL; // 获取总时间（秒）
                thh = tns / 3600; // 小时数
                tmm = (tns % 3600) / 60; // 分钟数
                tss = (tns % 60); // 秒数
                frac = x / cur_stream->width; // 计算点击位置的比例
                ns = frac * tns; // 根据比例计算当前时间（秒）
                hh = ns /3600; // 计算小时数
                mm = (ns % 3600) / 60; // 计算分钟数
                ss = (ns % 60); // 计算秒数
                av_log(NULL, AV_LOG_INFO,
                    "Seek to %2.0f%% (%2d:%02d:%02d) of total duration (%2d:%02d:%02d)       \n", frac * 100,
                    hh, mm, ss, thh, tmm, tss); // 日志输出跳转信息
                ts = frac * cur_stream->ic->duration; // 计算目标时间戳
                if (cur_stream->ic->start_time != AV_NOPTS_VALUE) // 如果有开始时间
                    ts += cur_stream->ic->start_time; // 加上开始时间
                stream_seek(cur_stream, ts, 0, 0); // 执行时间跳转
            }
            break;
        case SDL_WINDOWEVENT: // 窗口事件
            switch (event.window.event) {
            case SDL_WINDOWEVENT_SIZE_CHANGED: // 窗口大小改变事件
                screen_width = cur_stream->width = event.window.data1; // 更新宽度
                screen_height = cur_stream->height = event.window.data2; // 更新高度
                if (cur_stream->vis_texture) { // 如果有可视化纹理
                    SDL_DestroyTexture(cur_stream->vis_texture); // 销毁纹理
                    cur_stream->vis_texture = NULL; // 重置纹理指针
                }
            case SDL_WINDOWEVENT_EXPOSED: // 窗口暴露事件
                cur_stream->force_refresh = 1; // 强制刷新
            }
            break;
        case SDL_QUIT: // 退出事件
        case FF_QUIT_EVENT: // FFmpeg自定义退出事件
            do_exit(cur_stream); // 退出程序
            break;
        default: // 其他事件
            break;
        }
    }
}

//解析并设置屏幕宽度，确保其在合法范围内。
static int opt_width(void* optctx, const char* opt, const char* arg)
{
    screen_width = parse_number_or_die(opt, arg, OPT_INT64, 1, INT_MAX); // 解析并设置屏幕宽度，确保在合法范围内
    return 0; // 返回成功
}
//解析并设置屏幕高度，确保其在合法范围内。
static int opt_height(void* optctx, const char* opt, const char* arg)
{
    screen_height = parse_number_or_die(opt, arg, OPT_INT64, 1, INT_MAX); // 解析并设置屏幕高度，确保在合法范围内
    return 0; // 返回成功
}
//根据给定的格式字符串查找并设置输入格式，若未找到则记录错误并返回错误码。
static int opt_format(void* optctx, const char* opt, const char* arg)
{
    file_iformat = av_find_input_format(arg); // 根据给定的格式字符串查找输入格式
    if (!file_iformat) { // 如果未找到格式
        av_log(NULL, AV_LOG_FATAL, "Unknown input format: %s\n", arg); // 记录错误日志
        return AVERROR(EINVAL); // 返回错误码
    }
    return 0; // 返回成功
}

//根据传入的参数设置音视频同步的主时钟类型，支持音频、视频或外部时钟。
static int opt_sync(void *optctx, const char *opt, const char *arg)
{
    if (!strcmp(arg, "audio")) // 如果参数是"audio"
        av_sync_type = AV_SYNC_AUDIO_MASTER; // 设置为音频主同步
    else if (!strcmp(arg, "video")) // 如果参数是"video"
        av_sync_type = AV_SYNC_VIDEO_MASTER; // 设置为视频主同步
    else if (!strcmp(arg, "ext")) // 如果参数是"ext"
        av_sync_type = AV_SYNC_EXTERNAL_CLOCK; // 设置为外部时钟同步
    else { // 如果参数不匹配
        av_log(NULL, AV_LOG_ERROR, "Unknown value for %s: %s\n", opt, arg); // 记录错误日志
        exit(1); // 退出程序
    }
    return 0; // 返回0表示成功

}

//解析并设置视频播放的起始时间。
static int opt_seek(void *optctx, const char *opt, const char *arg)
{
    start_time = parse_time_or_die(opt, arg, 1); // 解析参数并设置起始时间
    return 0; // 返回0表示成功
}
//解析并设置视频播放的持续时间。
static int opt_duration(void *optctx, const char *opt, const char *arg)
{
    duration = parse_time_or_die(opt, arg, 1);// 解析参数并设置持续时间
    return 0;
}
//根据传入的参数设置显示模式，包括视频、波形或傅里叶变换等选项。
static int opt_show_mode(void *optctx, const char *opt, const char *arg)
{
    show_mode = !strcmp(arg, "video") ? SHOW_MODE_VIDEO : // 如果参数是"video"
        !strcmp(arg, "waves") ? SHOW_MODE_WAVES : // 如果参数是"waves"
        !strcmp(arg, "rdft") ? SHOW_MODE_RDFT : // 如果参数是"rdft"
        parse_number_or_die(opt, arg, OPT_INT, 0, SHOW_MODE_NB - 1); // 否则解析为数字
    return 0; // 返回0表示成功
}

//设置输入文件名，并检查是否已经指定了输入文件。
static void opt_input_file(void *optctx, const char *filename)
{
    if (input_filename) { // 如果已经有输入文件名
        av_log(NULL, AV_LOG_FATAL, // 记录致命错误日志
            "Argument '%s' provided as input filename, but '%s' was already specified.\n",
            filename, input_filename);
        exit(1); // 退出程序
    }
    if (!strcmp(filename, "-")) // 如果文件名是"-"
        filename = "fd:"; // 将其转换为"fd:"
    input_filename = filename; // 设置输入文件名

}

//解析并设置音频、视频或字幕的编解码器。
static int opt_codec(void *optctx, const char *opt, const char *arg)
{
    const char* spec = strchr(opt, ':'); // 查找冒号分隔符
    if (!spec) { // 如果没有找到
        av_log(NULL, AV_LOG_ERROR, // 记录错误日志
            "No media specifier was specified in '%s' in option '%s'\n",
            arg, opt);
        return AVERROR(EINVAL); // 返回错误
    }
    spec++; // 指向冒号后的字符
    switch (spec[0]) { // 根据指定的媒体类型进行分支
    case 'a': audio_codec_name = arg; break; // 音频编解码器
    case 's': subtitle_codec_name = arg; break; // 字幕编解码器
    case 'v': video_codec_name = arg; break; // 视频编解码器
    default: // 如果不匹配
        av_log(NULL, AV_LOG_ERROR, // 记录错误日志
            "Invalid media specifier '%s' in option '%s'\n", spec, opt);
        return AVERROR(EINVAL); // 返回错误
    }
    return 0; // 返回0表示成功

}

static int dummy;

//用于定义命令行选项，允许用户通过命令行参数来配置程序的行为
static const OptionDef options[] = {
    CMDUTILS_COMMON_OPTIONS  // 引入通用选项
    { "x", HAS_ARG, {.func_arg = opt_width }, "force displayed width", "width" },  // 设置显示宽度
    { "y", HAS_ARG, {.func_arg = opt_height }, "force displayed height", "height" },  // 设置显示高度
    { "fs", OPT_BOOL, { &is_full_screen }, "force full screen" },  // 强制全屏显示
    { "an", OPT_BOOL, { &audio_disable }, "disable audio" },  // 禁用音频
    { "vn", OPT_BOOL, { &video_disable }, "disable video" },  // 禁用视频
    { "sn", OPT_BOOL, { &subtitle_disable }, "disable subtitling" },  // 禁用字幕
    { "ast", OPT_STRING | HAS_ARG | OPT_EXPERT, { &wanted_stream_spec[AVMEDIA_TYPE_AUDIO] }, "select desired audio stream", "stream_specifier" },  // 选择所需音频流
    { "vst", OPT_STRING | HAS_ARG | OPT_EXPERT, { &wanted_stream_spec[AVMEDIA_TYPE_VIDEO] }, "select desired video stream", "stream_specifier" },  // 选择所需视频流
    { "sst", OPT_STRING | HAS_ARG | OPT_EXPERT, { &wanted_stream_spec[AVMEDIA_TYPE_SUBTITLE] }, "select desired subtitle stream", "stream_specifier" },  // 选择所需字幕流
    { "ss", HAS_ARG, {.func_arg = opt_seek }, "seek to a given position in seconds", "pos" },  // 设置播放起始位置
    { "t", HAS_ARG, {.func_arg = opt_duration }, "play  \"duration\" seconds of audio/video", "duration" },  // 播放指定持续时间的音视频
    { "bytes", OPT_INT | HAS_ARG, { &seek_by_bytes }, "seek by bytes 0=off 1=on -1=auto", "val" },  // 按字节寻址
    { "seek_interval", OPT_FLOAT | HAS_ARG, { &seek_interval }, "set seek interval for left/right keys, in seconds", "seconds" },  // 设置左右键的寻址间隔
    { "nodisp", OPT_BOOL, { &display_disable }, "disable graphical display" },  // 禁用图形显示
    { "noborder", OPT_BOOL, { &borderless }, "borderless window" },  // 设置无边框窗口
    { "alwaysontop", OPT_BOOL, { &alwaysontop }, "window always on top" },  // 窗口总在最上层
    { "volume", OPT_INT | HAS_ARG, { &startup_volume}, "set startup volume 0=min 100=max", "volume" },  // 设置启动音量
    { "f", HAS_ARG, {.func_arg = opt_format }, "force format", "fmt" },  // 强制设置格式
    { "stats", OPT_BOOL | OPT_EXPERT, { &show_status }, "show status", "" },  // 显示状态
    { "fast", OPT_BOOL | OPT_EXPERT, { &fast }, "non spec compliant optimizations", "" },  // 非规范优化
    { "genpts", OPT_BOOL | OPT_EXPERT, { &genpts }, "generate pts", "" },  // 生成PTS
    { "drp", OPT_INT | HAS_ARG | OPT_EXPERT, { &decoder_reorder_pts }, "let decoder reorder pts 0=off 1=on -1=auto", "" },  // 让解码器重新排序PTS
    { "lowres", OPT_INT | HAS_ARG | OPT_EXPERT, { &lowres }, "", "" },  // 设置低分辨率
    { "sync", HAS_ARG | OPT_EXPERT, {.func_arg = opt_sync }, "set audio-video sync. type (type=audio/video/ext)", "type" },  // 设置音视频同步类型
    { "autoexit", OPT_BOOL | OPT_EXPERT, { &autoexit }, "exit at the end", "" },  // 播放结束时自动退出
    { "exitonkeydown", OPT_BOOL | OPT_EXPERT, { &exit_on_keydown }, "exit on key down", "" },  // 按下键时退出
    { "exitonmousedown", OPT_BOOL | OPT_EXPERT, { &exit_on_mousedown }, "exit on mouse down", "" },  // 鼠标点击时退出
    { "loop", OPT_INT | HAS_ARG | OPT_EXPERT, { &loop }, "set number of times the playback shall be looped", "loop count" },  // 设置播放循环次数
    { "framedrop", OPT_BOOL | OPT_EXPERT, { &framedrop }, "drop frames when cpu is too slow", "" },  // CPU过慢时丢弃帧
    { "infbuf", OPT_BOOL | OPT_EXPERT, { &infinite_buffer }, "don't limit the input buffer size (useful with realtime streams)", "" },  // 不限制输入缓冲区大小
    { "window_title", OPT_STRING | HAS_ARG, { &window_title }, "set window title", "window title" },  // 设置窗口标题
    { "left", OPT_INT | HAS_ARG | OPT_EXPERT, { &screen_left }, "set the x position for the left of the window", "x pos" },  // 设置窗口左边的位置
    { "top", OPT_INT | HAS_ARG | OPT_EXPERT, { &screen_top }, "set the y position for the top of the window", "y pos" },  // 设置窗口顶部的位置
#if CONFIG_AVFILTER
    { "vf", OPT_EXPERT | HAS_ARG, {.func_arg = opt_add_vfilter }, "set video filters", "filter_graph" },  // 设置视频过滤器
    { "af", OPT_STRING | HAS_ARG, { &afilters }, "set audio filters", "filter_graph" },  // 设置音频过滤器
#endif
    { "rdftspeed", OPT_INT | HAS_ARG | OPT_AUDIO | OPT_EXPERT, { &rdftspeed }, "rdft speed", "msecs" },  // 设置RDFT速度
    { "showmode", HAS_ARG, {.func_arg = opt_show_mode}, "select show mode (0 = video, 1 = waves, 2 = RDFT)", "mode" },  // 选择显示模式
    { "i", OPT_BOOL, { &dummy}, "read specified file", "input_file"},  // 读取指定文件
    { "codec", HAS_ARG, {.func_arg = opt_codec}, "force decoder", "decoder_name" },  // 强制设置解码器
    { "acodec", HAS_ARG | OPT_STRING | OPT_EXPERT, { &audio_codec_name }, "force audio decoder", "decoder_name" },  // 强制设置音频解码器
    { "scodec", HAS_ARG | OPT_STRING | OPT_EXPERT, { &subtitle_codec_name }, "force subtitle decoder", "decoder_name" },  // 强制设置字幕解码器
    { "vcodec", HAS_ARG | OPT_STRING | OPT_EXPERT, { &video_codec_name }, "force video decoder", "decoder_name" },  // 强制设置视频解码器
    { "autorotate", OPT_BOOL, { &autorotate }, "automatically rotate video", "" },  // 自动旋转视频
    { "find_stream_info", OPT_BOOL | OPT_INPUT | OPT_EXPERT, { &find_stream_info }, "read and decode the streams to fill missing information with heuristics" },  // 读取并解码流以填充缺失信息
    { "filter_threads", HAS_ARG | OPT_INT | OPT_EXPERT, { &filter_nbthreads }, "number of filter threads per graph" },  // 设置每个过滤图的线程数量
    { NULL, },  // 结束选项定义
};


static void show_usage(void) // 用于显示程序的使用说明
{
    av_log(NULL, AV_LOG_INFO, "Simple media player\n"); // 输出简单媒体播放器的标题
    av_log(NULL, AV_LOG_INFO, "usage: %s [options] input_file\n", program_name); // 输出使用方法，包括程序名称和参数格式
    av_log(NULL, AV_LOG_INFO, "\n"); // 输出一个空行，增加可读性
}

//展示程序的帮助信息，包括基本用法、可用选项和播放时的控制操作。
void show_help_default(const char* opt, const char* arg) // 定义函数，用于显示帮助信息
{
    av_log_set_callback(log_callback_help); // 设置日志回调，以便输出帮助信息
    show_usage(); // 调用函数显示程序的基本使用信息
    show_help_options(options, "Main options:", 0, OPT_EXPERT, 0); // 显示主要选项的帮助信息
    show_help_options(options, "Advanced options:", OPT_EXPERT, 0, 0); // 显示高级选项的帮助信息
    printf("\n"); // 输出空行以增强可读性
    show_help_children(avcodec_get_class(), AV_OPT_FLAG_DECODING_PARAM); // 显示解码参数的帮助信息
    show_help_children(avformat_get_class(), AV_OPT_FLAG_DECODING_PARAM); // 显示格式参数的帮助信息
#if !CONFIG_AVFILTER // 如果没有配置过滤器
    show_help_children(sws_get_class(), AV_OPT_FLAG_ENCODING_PARAM); // 显示缩放参数的帮助信息
#else // 如果配置了过滤器
    show_help_children(avfilter_get_class(), AV_OPT_FLAG_FILTERING_PARAM); // 显示过滤器参数的帮助信息
#endif
    printf("\nWhile playing:\n" // 输出播放时可用的操作说明
        "q, ESC              quit\n" // 按q或ESC退出
        "f                   toggle full screen\n" // 按f切换全屏
        "p, SPC              pause\n" // 按p或空格键暂停
        "m                   toggle mute\n" // 按m静音/取消静音
        "9, 0                decrease and increase volume respectively\n" // 按9和0调整音量
        "/, *                decrease and increase volume respectively\n" // 按/和*调整音量
        "a                   cycle audio channel in the current program\n" // 按a切换音频频道
        "v                   cycle video channel\n" // 按v切换视频频道
        "t                   cycle subtitle channel in the current program\n" // 按t切换字幕频道
        "c                   cycle program\n" // 按c切换程序
        "w                   cycle video filters or show modes\n" // 按w切换视频过滤器或显示模式
        "s                   activate frame-step mode\n" // 按s激活逐帧模式
        "left/right          seek backward/forward 10 seconds or to custom interval if -seek_interval is set\n" // 左右键快退/快进10秒
        "down/up             seek backward/forward 1 minute\n" // 上下键快退/快进1分钟
        "page down/page up   seek backward/forward 10 minutes\n" // PageDown/PageUp快退/快进10分钟
        "right mouse click   seek to percentage in file corresponding to fraction of width\n" // 右键点击按比例跳转
        "left double-click   toggle full screen\n" // 左键双击切换全屏
    );
}


//主要作用是初始化媒体播放器，处理命令行参数，设置SDL环境，创建窗口和渲染器，然后进入事件循环以处理媒体播放。
int main(int argc, char** argv) // 主函数，程序入口
{
    int flags; // 用于存储SDL初始化标志
    VideoState* is; // 视频状态结构体指针

    //重点
    init_dynload(); // 初始化动态加载

    av_log_set_flags(AV_LOG_SKIP_REPEATED); // 设置日志标志，跳过重复日志
    parse_loglevel(argc, argv, options); // 解析日志级别选项

    /* register all codecs, demux and protocols */
#if CONFIG_AVDEVICE
    avdevice_register_all(); // 注册所有设备
#endif
    avformat_network_init(); // 初始化网络格式

    signal(SIGINT, sigterm_handler); // 捕获中断信号
    signal(SIGTERM, sigterm_handler); // 捕获终止信号

    //重点
    show_banner(argc, argv, options); // 显示程序横幅

    parse_options(NULL, argc, argv, options, opt_input_file); // 解析命令行选项

    if (!input_filename) { // 检查是否指定输入文件
        show_usage(); // 显示用法
        av_log(NULL, AV_LOG_FATAL, "An input file must be specified\n"); // 错误日志
        av_log(NULL, AV_LOG_FATAL,
            "Use -h to get full help or, even better, run 'man %s'\n", program_name);
        exit(1); // 退出程序
    }

    //重点
    if (display_disable) { // 如果禁用显示
        video_disable = 1; // 禁用视频
    }
    flags = SDL_INIT_VIDEO | SDL_INIT_AUDIO | SDL_INIT_TIMER; // 设置SDL初始化标志
    if (audio_disable) // 如果禁用音频
        flags &= ~SDL_INIT_AUDIO; // 移除音频标志
    else {
        // 处理可能的ALSA缓冲区下溢问题
        if (!SDL_getenv("SDL_AUDIO_ALSA_SET_BUFFER_SIZE"))
            SDL_setenv("SDL_AUDIO_ALSA_SET_BUFFER_SIZE", "1", 1); // 强制设置缓冲区大小
    }
    if (display_disable) // 如果禁用显示
        flags &= ~SDL_INIT_VIDEO; // 移除视频标志
    if (SDL_Init(flags)) { // 初始化SDL
        av_log(NULL, AV_LOG_FATAL, "Could not initialize SDL - %s\n", SDL_GetError()); // 错误日志
        av_log(NULL, AV_LOG_FATAL, "(Did you set the DISPLAY variable?)\n"); // 错误提示
        exit(1); // 退出程序
    }

    SDL_EventState(SDL_SYSWMEVENT, SDL_IGNORE); // 忽略系统事件
    SDL_EventState(SDL_USEREVENT, SDL_IGNORE); // 忽略用户事件

    if (!display_disable) { // 如果未禁用显示
        int flags = SDL_WINDOW_HIDDEN; // 初始化窗口标志为隐藏
        if (alwaysontop) // 如果总在最上面
#if SDL_VERSION_ATLEAST(2,0,5)
            flags |= SDL_WINDOW_ALWAYS_ON_TOP; // 设置为总在最上面
#else
            av_log(NULL, AV_LOG_WARNING, "Your SDL version doesn't support SDL_WINDOW_ALWAYS_ON_TOP. Feature will be inactive.\n"); // 警告日志
#endif
        if (borderless) // 如果无边框
            flags |= SDL_WINDOW_BORDERLESS; // 设置为无边框
        else
            flags |= SDL_WINDOW_RESIZABLE; // 否则设置为可调整大小

#ifdef SDL_HINT_VIDEO_X11_NET_WM_BYPASS_COMPOSITOR
        SDL_SetHint(SDL_HINT_VIDEO_X11_NET_WM_BYPASS_COMPOSITOR, "0"); // 设置提示
#endif
        window = SDL_CreateWindow(program_name, SDL_WINDOWPOS_UNDEFINED, SDL_WINDOWPOS_UNDEFINED, default_width, default_height, flags); // 创建窗口
        SDL_SetHint(SDL_HINT_RENDER_SCALE_QUALITY, "linear"); // 设置渲染质量为线性
        if (window) { // 如果窗口创建成功
            renderer = SDL_CreateRenderer(window, -1, SDL_RENDERER_ACCELERATED | SDL_RENDERER_PRESENTVSYNC); // 创建渲染器
            if (!renderer) { // 如果渲染器创建失败
                av_log(NULL, AV_LOG_WARNING, "Failed to initialize a hardware accelerated renderer: %s\n", SDL_GetError()); // 警告日志
                renderer = SDL_CreateRenderer(window, -1, 0); // 创建软件渲染器
            }
            if (renderer) { // 如果渲染器创建成功
                if (!SDL_GetRendererInfo(renderer, &renderer_info)) // 获取渲染器信息
                    av_log(NULL, AV_LOG_VERBOSE, "Initialized %s renderer.\n", renderer_info.name); // 日志输出渲染器名称
            }
        }
        if (!window || !renderer || !renderer_info.num_texture_formats) { // 检查窗口、渲染器和纹理格式
            av_log(NULL, AV_LOG_FATAL, "Failed to create window or renderer: %s", SDL_GetError()); // 错误日志
            do_exit(NULL); // 退出程序
        }
    }

    //重点
    is = stream_open(input_filename, file_iformat); // 打开输入流
    if (!is) { // 如果打开失败
        av_log(NULL, AV_LOG_FATAL, "Failed to initialize VideoState!\n"); // 错误日志
        do_exit(NULL); // 退出程序
    }

    event_loop(is); // 进入事件循环

    /* never returns */ // 函数不会返回

    return 0; // 返回0，表示程序正常结束
}

