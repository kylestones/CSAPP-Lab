/*
 * 文档中给出的编码格式要求
 * 1. Your code should be decomposed into functions and use as few global variables as possible. You
 * should use macros or inline functions to isolate pointer arithmetic to as few places as possible.
 *
 * 1. Your code must begin with a header comment that gives an overview of the structure of your free and
 * allocated blocks, the organization of the free list, and how your allocator manipulates the free list.
 *
 * 1. In addition to this overview header comment, each function should be preceded by a header comment
 * that describes what the function does.
 *
 * 整体设计：
 * 1. 每个 block 至少为 4 个指针大小，hdrp - pred - succ - ftrp ，依次为 头指针、前驱指针、后继指针、脚指针
 * 1. 分离空闲链表，有 9 个入口 {32}, {33-64}, {65-128}, {129-512}, {513-1024}, {1025-2048}, {2049-4096}, {4097-INC}
 * 1. 每个空闲链表入口包含两个指针，pred 和 succ ，用于消除头部的特殊处理
 * 1. 空闲链表的入口保存在堆的起始位置，使用一个全局变量保存首地址，供占据 2 * 9 * SIZE_T_SIZE 大小
 * 1. 为了保持 32 位兼容，堆空间上，空闲链表入口地址只有仍然保留一个 SIZE_T_SIZE 大小的对齐空间
 *
 * 编码：
 * 1. 拆分了一些函数
 * 1. 使用了两个全局变量，一个保存空闲链表的入口地址，另一个保存序言块的起始地址（这个好像也不太需要。。）
 * 1. 设计到指针的特殊处理，基本都使用了宏定义
 * 1. 函数头，对函数的主意事项进行了必要的描述
 *
 * 活动：
 * 20201001 -- 阅读 csapp
 * 20201003 -- 开始书写
 * 20201005 -- 功能函数基本完成
 * 20201006 -- 开始调试，，增加了堆的检查函数，居然检查函数写错了好几个地方，后来发现最小块大小有问题，24 的时候，在空闲链表上无法正常保存，晚上可以跑通，但是分数很低
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdlib.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
//#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* expand heap by this amount (bytes) */
#define CHUNKSIZE (1<<12)
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
/* hdr ftr pred succ -- size  自动适配 32 64 位系统 */
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
/* block 最小值 header footer pred succ */
#define MIN_BLOCK_SIZE (8 + 8 + 8 + 8)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - SIZE_T_SIZE))

/* pack size and allocated bit */
#define PACK(size, alloc)  ((size) | (alloc))

/* read and write -- at address p */
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = val)

/* read the size and allocated bit from address p */
#define GET_SIZE(p)   (GET(p) & ~0x7)
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, computer address of its header and footer */
#define HDRP(bp)  ((char *)(bp) - SIZE_T_SIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - 2 * SIZE_T_SIZE)

/* Given block ptr bp, computer address of previous and next blocks */
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE((char *)(bp) - 2 * SIZE_T_SIZE))
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)))

/*
 * 定义空闲链表的前驱和后继的时候，发现有点迷茫
 * something about pointer:
 * 1. 普通变量，有变量名、类型、值
 * 1. 变量名--对应该变量的地址，类型--数据的类型，值--实际数据
 * 1. 指针是一个变量，有变量名、类型、值
 * 1. 变量名--对应内存中某个地址，类型--某种类型的指针，值--某个对应类型变量的地址
 * 1. 指针的指针也是一个变量，有变量名、类型、值
 * 1. 变量名--同样也是内存中某个地址，类型--某种类型指针的指针，值--指向某种类型数据指针的地址
 * 1. 不管什么类型的指针， * 操作都是得到该指针指向的值
 */
/* Given free block ptr bp, compute address of its preceding free block and succeeding block */
#define PRED_BLKP(bp)  (*(char **)(bp))
#define SUCC_BLKP(bp)  (*(char **)((char *)(bp) + SIZE_T_SIZE))


/*
  64 位系统，hdr + ftr + pred + succ = 8+ 8 + 8 + 8 = 32
    16 - 32
    33 - 64
    65 - 128
   129 - 256
   257 - 512
   513 - 1024
  1025 - 2048
  2049 - 4096
  4097 - INF
  共 9 组，每组保存 pred succ 两个指针
 */
#define SEGREGATED_FREE_LIST_NUM        (9)
#define SEGREGATED_FREE_LIST_ENTRY_STEP (2)
#define SEGREGATED_FREE_LIST_ENTRY_SIZE (SEGREGATED_FREE_LIST_NUM * SEGREGATED_FREE_LIST_ENTRY_STEP)

// global variable
static size_t *segregated_free_listp = NULL;
static char   *heap_listp            = NULL;

#define MEM_SUCCESS (0)
#define MEM_ERROR   (-1)

/* 内部函数声明 */
static void *extend_heap(size_t bytes);
static void *coalesce(void *bp);
static void *find_fit(size_t size);
static void place(void *bp, size_t asize);
static size_t *find_entry_in_segregated_list(size_t size);
static int insert_to_segregated_list(void *bp);
static int delete_from_segregated_list(void *bp);
static void mm_print_heap();

/*
 * mm_init - Called when a new trace starts.
 * 作用：
 * 1. 初始化空闲链表
 * 1. 是否需要额外的空间对齐 -- 64 位始终不需要，32 位需要关注分离空闲链表的个数
 * 1. 初始化序言块和结尾块
 * 1. 申请一定大小的空间，调用 extend_heap 函数实现
 */
int mm_init(void)
{
    // 2 * 9 ，前面是偶数个，32 位的时候，仍然需要保留一个 SIZE_T_SIZE 对齐
    heap_listp = (char *)mem_sbrk((SEGREGATED_FREE_LIST_ENTRY_SIZE + 4) * SIZE_T_SIZE);
    if ((void *)heap_listp == (void *)MEM_ERROR)
    {
        return MEM_ERROR;
    }

    // 堆的开始位置保存空闲链表数组
    segregated_free_listp = (size_t *)heap_listp;
    // 初始化空闲链表全部为空
    memset(segregated_free_listp, 0, SEGREGATED_FREE_LIST_ENTRY_SIZE * SIZE_T_SIZE);

    // heap_listp 跳过空闲链表数组
    heap_listp += SEGREGATED_FREE_LIST_ENTRY_SIZE * SIZE_T_SIZE;
    // 初始化序言块 prologue block 和结尾块 epilogue block
    PUT(heap_listp, 0); /* 32 位的时候，需要的对齐块 */
    PUT(heap_listp + 1 * SIZE_T_SIZE, PACK(2 * SIZE_T_SIZE, 1)); /* prologue header */
    PUT(heap_listp + 2 * SIZE_T_SIZE, PACK(2 * SIZE_T_SIZE, 1)); /* prologue footer */
    PUT(heap_listp + 3 * SIZE_T_SIZE, PACK(0, 1)); /* epilogue header */

    // 指向序言块的中间
    heap_listp += 2 * SIZE_T_SIZE;

    // 扩张块
    if (extend_heap(CHUNKSIZE) == NULL)
    {
        return -1;
    }

#ifdef DEBUG
    mm_checkheap(__LINE__);
#endif
    return 0;
}

/*
 * malloc - Allocate a block
 *      Always allocate a block whose size is a multiple of the alignment.
 *
 * 1. 调整 size ，满足对齐和最小块的要求（请求的大小需要先加上 header 和 footer 大小）
 * 1. 调用 find_fit 搜索合适的 block
 * 1. 如果找到，调用 place
 * 1. 无论是否找到，都返回 bp （未找到时， bp = NULL）
 */
void *malloc(size_t size)
{
    if (size == 0)
    {
        return NULL;
    }

    /* adjusted block size */
    size_t asize = 0;
    void   *bp   = NULL;

    // 满足最小块的要求
    if (size <= SIZE_T_SIZE)
    {
        asize = MIN_BLOCK_SIZE;
    }
    else
    {
        asize = ALIGN(size + 2 * SIZE_T_SIZE);
    }

    // 查找合适的 block ，此处不关心具体实现算法
    // 如果空闲链表中没有合适的 block ，find_fit 会扩张堆的大小
    bp = find_fit(asize);

    // 如果找到了合适的 block
    if (bp != NULL)
    {
        place(bp, asize);
        dbg_printf("malloc size %lu, asize %lu => %p\n", size, asize, bp);
    }

#ifdef DEBUG
    mm_checkheap(__LINE__);
#endif
    // 没有找到合适的 block ，bp = NULL
    return bp;
}

/*
 * free - 释放之前分配的 block
 *
 * 1. 主要需要清空 allocated bit ，合并，加入空闲链表
 * 1. 这里只需要调用 coalesce 函数即可
 */
void free(void *ptr){
    if (ptr != NULL)
    {
        dbg_printf("free size %lu => %p\n", GET_SIZE(HDRP(ptr)), ptr);
        // 不需要设置 header 和 footer ，直接调用合并函数就可以了
        coalesce(ptr);
#ifdef DEBUG
        mm_checkheap(__LINE__);
#endif
    }
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.  I'm too lazy
 *      to do better.
 * TODO - 暂未处理
 */
void *realloc(void *oldptr, size_t size)
{
  size_t oldsize;
  void *newptr;

  /* If size == 0 then this is just free, and we return NULL. */
  if(size == 0) {
    free(oldptr);
    return 0;
  }

  /* If oldptr is NULL, then this is just malloc. */
  if(oldptr == NULL) {
    return malloc(size);
  }

  newptr = malloc(size);

  /* If realloc() fails the original block is left untouched  */
  if(!newptr) {
    return 0;
  }

  /* Copy the old data. */
  oldsize = *SIZE_PTR(oldptr);
  if(size < oldsize) oldsize = size;
  memcpy(newptr, oldptr, oldsize);

  /* Free the old block. */
  free(oldptr);

  return newptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc (size_t nmemb, size_t size)
{
  size_t bytes = nmemb * size;
  void *newptr;

  newptr = malloc(bytes);
  memset(newptr, 0, bytes);

  return newptr;
}

/*
 * 堆空间无法继续分配需要的空间，通过系统调用扩展堆的大小
 * 只在两个地方调用：初始化和 find_fit (not malloc)
 *
 * 作用：
 * 1. 保证扩展的 block 大小符合对齐要求
 * 1. 初始化新 block 的头部（占用了原来结尾块的空间）和脚部
 * 1. 设置新的结尾块
 * 1. 前面 block 可能是 free 的，需要合并块，不需要显著将合并后的 block 加入空闲链表，coalesce 函数中会处理
 */
static void *extend_heap(size_t bytes)
{
    char   *bp   = NULL;
    size_t asize = 0;

    if (bytes < MIN_BLOCK_SIZE)
    {
        asize = MIN_BLOCK_SIZE;
    }
    else
    {
        asize = ALIGN(bytes);
    }

    // 分配的大小满足对齐要求
    bp = (char *)mem_sbrk(asize);
    if ((void *)bp == (void *)MEM_ERROR)
    {
        return NULL;
    }

    // 初始化新的空闲块 header footer
    PUT(HDRP(bp), PACK(asize, 0));
    PUT(FTRP(bp), PACK(asize, 0));
    // 设置尾块
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    // 前面的块可能是 free block ，coalesce 会将新申请的 block 加入分离空闲链表
    return coalesce(bp);
}

/*
 * 如果空闲 block 地址紧邻的前后 block 是 free 的，需要合并块
 * 不会出现前面或者后面连续的 block （否则之前的状态有问题），就是说合并操作不需要递归或者循环
 *
 * 作用：
 * 1. 处理四种情况下的合并： 前 A 后 A 、前 A 后 F 、前 F 后 A 、前 F 后 F
 * 1. 如果前后或后面的块有是 free 状态的，需要将其从分离空闲链表摘除
 * 1. 合并 block ，先计算 size ，必须先设置合并后地址的 header ，然后设置 footer
 * 1. 合并后的空闲链表，加入分离空闲链表中
 * 1. 返回值是合并后的 free block 的地址，如果前面 block 是 free 的，那么返回值是前面 block 的地址
 */

static void *coalesce(void *bp)
{
    char   *prev      = PREV_BLKP(bp);
    char   *next      = NEXT_BLKP(bp);
    // 因为有序言块和结尾块，这里不需要额外的判断
    size_t prev_alloc = GET_ALLOC(HDRP(prev));
    size_t next_alloc = GET_ALLOC(HDRP(next));
    size_t size       = GET_SIZE(HDRP(bp));

    // 前 A 后 A
    if (prev_alloc && next_alloc)
    {
        // 直接加入到分离空闲链表就可以了
        insert_to_segregated_list(bp);
    }

    // 前 A 后 F
    else if (prev_alloc && !next_alloc)
    {
        // 将 next free block 从空闲链表删除
        delete_from_segregated_list(next);
        // 合并后新 block 的 size
        size += GET_SIZE(HDRP(next));
        // 设置合并后 block 的 header 和 footer
        PUT(HDRP(bp), PACK(size, 0x0));
        PUT(FTRP(bp), PACK(size, 0x0));
        // 插入空闲链表
        insert_to_segregated_list(bp);
    }

    // 前 F 后 A
    else if (!prev_alloc && next_alloc)
    {
        // 将 prev free block 从空闲链表删除
        delete_from_segregated_list(prev);
        // 合并后新 block 的 size
        size += GET_SIZE(HDRP(prev));
        // 合并后的 block 是前面 block 的地址
        bp = prev;
        // 设置合并后 block 的 header 和 footer
        PUT(HDRP(bp), PACK(size, 0x0));
        PUT(FTRP(bp), PACK(size, 0x0));
        // 插入空闲链表
        insert_to_segregated_list(bp);
    }

    // 前 A 后 A
    else
    {
        // 将 prev 和 next free block 从空闲链表删除
        delete_from_segregated_list(prev);
        delete_from_segregated_list(next);
        // 合并后新 block 的 size
        size += GET_SIZE(HDRP(prev)) + GET_SIZE(HDRP(next));
        // 合并后的 block 是前面 block 的地址
        bp = prev;
        // 设置合并后 block 的 header 和 footer
        PUT(HDRP(bp), PACK(size, 0x0));
        PUT(FTRP(bp), PACK(size, 0x0));
        // 插入空闲链表
        insert_to_segregated_list(bp);
    }

#ifdef DEBUG
    mm_checkheap(__LINE__);
#endif
    return bp;
}

/*
 * 分离空闲链表的入口，如果只使用一个指针，开头都需要做特殊处理
 * 因此使用空间换取时间的方法，每个入口（头节点）使用两个指针的空间，
 * 分别保存 perd 和 succ 两个指针，和正常的空闲块一样（这样在链表头节点不再需要特殊处理）
 * 但是头节点并没有 header 和 footer 空间，不可以在头节点获取块的大小，头节点默认块大小为 0
 */

/*
 * 查找对应的分离空闲链表入口
 * 作用：
 * 1. 根据 size 的大小，返回对应链表的起始地址
 *
 * 这里这么的 if 效率肯定会特别的低，待优化 TODO
 * 也可以根据需要修改这个函数的实现，不影响其他的功能
 */
static size_t *find_entry_in_segregated_list(size_t size)
{
    if (size <= 32)
    {
        return segregated_free_listp;
    }
    else if (size <= 64)
    {
        return segregated_free_listp + 1 * 2;
    }
    else if (size <= 128)
    {
        return segregated_free_listp + 2 * 2;
    }
    else if (size <= 256)
    {
        return segregated_free_listp + 3 * 2;
    }
    else if (size <= 512)
    {
        return segregated_free_listp + 4 * 2;
    }
    else if (size <= 1024)
    {
        return segregated_free_listp + 5 * 2;
    }
    else if (size <= 2048)
    {
        return segregated_free_listp + 6 * 2;
    }
    else if (size <= 4096)
    {
        return segregated_free_listp + 7 * 2;
    }
    else
    {
        return segregated_free_listp + 8 * 2;
    }
}

/*
 * 将新分配或者释放合并后的 block 加入到分离空闲链表
 *
 * 1. 插入前 block 的 pred 和 succ 指针是无效的；但 header 和 footer 中的 size 必然是有效的，否则不是一个正确的 block
 * 1. 清空 allocated bit -- TODO
 * 1. 获取 block 的 size ，得到分离空闲链表的头节点
 * 1. 插入的时候，头节点同样不需要特殊的处理
 * 1. 是否在尾节点插入需要特殊判断
 */
static int insert_to_segregated_list(void *bp)
{
    if (bp == NULL)
    {
        return MEM_ERROR;
    }

    size_t size = GET_SIZE(HDRP(bp));
#if 1
    // 清空 allocated bit
    PUT(HDRP(bp), PACK(size, 0x0));
    PUT(FTRP(bp), PACK(size, 0x0));
#endif

    // pred 指向空闲链表中待插入节点的前一个节点
    // succ 指向空闲链表中待插入节点的后一个节点
    // bp 插入 prev 和 next 中间
    char *pred = (char *)find_entry_in_segregated_list(size);
    char *succ = SUCC_BLKP(pred);

    while (succ != NULL && size > GET_SIZE(succ))
    {
        pred = succ;
        succ = SUCC_BLKP(succ);
    }

    // 先设置待插入节点的前驱和后继
    PRED_BLKP(bp) = pred;
    SUCC_BLKP(bp) = SUCC_BLKP(pred);
    // 设置前驱的后继
    SUCC_BLKP(pred) = bp;
    // 设置后继的前驱
    if (succ != NULL)
    {
        PRED_BLKP(succ) = bp;
    }

    return MEM_SUCCESS;
}

/*
 * 将指定的 block 从分离空闲链表中删除
 *
 * 1. 置位 allocated bit ；从分离空闲链表删除，表明其是分配 TODO 要不要在这里处理呢？
 * 1. 被删除的 block 的 pred 肯定存在，不需要额外的判断；而且也不需要关心空闲链表的入口位置
 * 1. 被删除的 block 的 succ 不一定存在，是否为空，需要特殊处理

 * 双向链表删除操作
 * bp->prev->next = bp->next;
 * bp->next->prev = bp->prev;
 */
static int delete_from_segregated_list(void *bp)
{
    if (bp == NULL)
    {
        return MEM_ERROR;
    }

#if 1
    // 置位 allocated bit
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0x1));
    PUT(FTRP(bp), PACK(size, 0x1));
#endif

    char *pred = PRED_BLKP(bp);
    char *succ = SUCC_BLKP(bp);

    SUCC_BLKP(pred) = succ;

    if (succ != NULL)
    {
        PRED_BLKP(succ) = pred;
    }

    return MEM_SUCCESS;
}

/*
 * first fit 查找合适的 block ，未找到则扩张堆的大小
 * csapp 上面查找不到合适的 block 是在 malloc 函数中扩张堆的大小，
 * 但是我感觉在 find_fit 函数中实现更合理，因为这个函数就是为了找到合适的 block ，供其他函数调用
 *
 * 使用分离空闲链表，且按照 block 的大小排序，first fist 就是 best fit
 * 1. 先已经需要的 size 找到分离空闲链表的头节点
 * 1. 在该空闲链表上面无法找到满足需要 size 的 block ，则查找后一个空闲链表，知道最后一个空闲链表
 * 1. 如果仍然查找不到，则需要 extend_heap
 */
static void *find_fit(size_t asize)
{
    void *bp = NULL;

    if (asize == 0)
    {
        return NULL;
    }

    size_t *entry_listp = find_entry_in_segregated_list(asize);
    // 外循环遍历分离空闲链表的所有入口
    while (entry_listp < segregated_free_listp + SEGREGATED_FREE_LIST_ENTRY_SIZE)
    {
        // 内循环遍历单个空闲链表
        char *pred = (char *)entry_listp;
        char *succ = SUCC_BLKP(pred);
        while (succ != NULL && asize > GET_SIZE(HDRP(succ)))
        {
            pred = succ;
            succ = SUCC_BLKP(succ);
        }

        // 如果 succ 不为空，说明找到了合适的 block
        if (succ != NULL)
        {
            bp = (void *)succ;
            break;
        }

        entry_listp += SEGREGATED_FREE_LIST_ENTRY_STEP;
    }

    // 空闲链表中没有满足要求的 block
    if (bp == NULL)
    {
        // 扩展堆的大小是 asize 和 CHUNKSIZE 中的较大者
        // 扩张块，如果扩张失败 bp 仍然是 NULL
        bp = extend_heap(MAX(asize, CHUNKSIZE));
    }

    return bp;
}

/*
 * 入参：
 * bp 是查找到的 free block
 * asize 需要的 block size
 *
 * 1. 将 bp 从空闲链表删除（无论是否分割都需要处理）
 * 1. 当 bp 的 size 减去 asize 剩余的部分大于最小块时，需要将 bp 分割成两部分
 * 1. 将分割后剩余的 block 插入空闲链表
 */
static void place(void *bp, size_t asize)
{
    size_t split_size = GET_SIZE(HDRP(bp)) - asize;

    // 从空闲链表删除会设置 allocated bit
    if (delete_from_segregated_list(bp) != MEM_SUCCESS)
    {
        dbg_printf("%s-%s-%d\n", __FILE__, __func__, __LINE__);
        return;
    }

    if (split_size >= MIN_BLOCK_SIZE)
    {
        // 修改 header 和 footer 的 size 和 allocated bit
        PUT(HDRP(bp), PACK(asize, 0x1));
        PUT(FTRP(bp), PACK(asize, 0x1));

        // 分割后剩余的 block
        char *split_bp = NEXT_BLKP(bp);

        // 设置其 header 和 footer
        PUT(HDRP(split_bp), PACK(split_size, 0x0));
        PUT(FTRP(split_bp), PACK(split_size, 0x0));

        // 插入空闲链表
        if (insert_to_segregated_list(split_bp) != MEM_SUCCESS)
        {
            dbg_printf("%s-%s-%d\n", __FILE__, __func__, __LINE__);
        }
    }
#ifdef DEBUG
    mm_checkheap(__LINE__);
#endif
}


static void mm_print_heap()
{
    // 从序言块后一个节点开始往后遍历
    char *bp = heap_listp;
    size_t block_num = 0;
    // 只有结尾块的 size 是 0
    dbg_printf("ALL BLOCKS--------\n");
    while (GET_SIZE(HDRP(bp)))
    {
        block_num++;
        dbg_printf("block: %4lu - addr: %p - Halloc: %lu - Falloc: %lu - Hsize: %4lu - Fsize: %4lu\n",
                   block_num, bp,
                   GET_ALLOC(HDRP(bp)), GET_ALLOC(FTRP(bp)),
                   GET_SIZE(HDRP(bp)),  GET_SIZE(FTRP(bp)));

        bp = NEXT_BLKP(bp);
    }


    dbg_printf("\nFREE LISTS--------\n");
    size_t *entry_listp = segregated_free_listp;
    // 外循环遍历分离空闲链表的所有入口
    while (entry_listp < segregated_free_listp + SEGREGATED_FREE_LIST_ENTRY_SIZE)
    {
        // 内循环遍历单个空闲链表
        char *pred = (char *)entry_listp;
        char *succ = SUCC_BLKP(pred);
        while (succ != NULL)
        {
            dbg_printf("block: %lu - addr: %p - alloc: %lu -size: %lu\n", block_num, succ, GET_ALLOC(HDRP(succ)), GET_SIZE(HDRP(succ)));

            // 开始下一个节点的检查
            pred = succ;
            succ = SUCC_BLKP(succ);
        }

        entry_listp += SEGREGATED_FREE_LIST_ENTRY_STEP;
    }
}

/*
 * mm_checkheap - 检查 heap 和 free list
 *
 * checking the heap -- 通过 header footer 检查
 * 1. 检查 epilogue 和 prologue
 * 1. 检查 block's address alignment
 * 1. 检查堆的边界
 * 1. 检查 header 和 footer 是否匹配，是否存在连续的 free block
 *
 * checking the free list -- 通过 pred 和 succ
 * 1. pred/succ 是连续的， A's next is B, then B's pred must be A
 * 1. 所有的空闲链表都在 mem_heap_lo() 和 mem_heap_hight() 之间
 * 1. 通过 header footer 计算 free block 的个数，等于通过 pred succ 得到的个数
 * 1. 分离空闲链表中，各个 free block size 在该链表的范围之内
 */
void mm_checkheap(int verbose)
{
    verbose = verbose;
    dbg_printf("call by line-%d\n", verbose);

    /* checking the heap */

    /*
     * 检查 block's address alignment
     * 检查 header 和 footer 是否匹配
     * 检查是否存在连续的 free block
     */
    // 从序言块后一个节点开始往后遍历
    char *bp = NEXT_BLKP(heap_listp);
    size_t is_pre_alloc = 1;
    size_t free_block_num = 0;
    // 只有结尾块的 size 是 0
    while (GET_SIZE(HDRP(bp)))
    {
        // 检查地址对齐
        if (((size_t)bp % ALIGNMENT) != 0)
        {
            dbg_printf("%s-%s-%d\n", __FILE__, __func__, __LINE__);
            exit(127);
        }

        // 检查 header 和 footer 是否匹配
        if (GET(HDRP(bp)) != GET(FTRP(bp)))
        {
            dbg_printf("%s-%s-%d\n", __FILE__, __func__, __LINE__);
            exit(127);
        }

        // 前面块和当前块都是 free 的
        if (!is_pre_alloc && !GET_ALLOC(HDRP(bp)))
        {
            dbg_printf("%s-%s-%d\n", __FILE__, __func__, __LINE__);
            exit(127);
        }

        is_pre_alloc = GET_ALLOC(HDRP(bp));
        if (!is_pre_alloc)
        {
            free_block_num++;
        }

        bp = NEXT_BLKP(bp);
    }

    //检查 epilogue 和 prologue
    // 退出 while 循环后 bp 指向了结尾块
    if (GET(HDRP(bp)) != 0x1)
    {
        dbg_printf("%s-%s-%d\n", __FILE__, __func__, __LINE__);
        exit(127);
    }

#define PROLOGUE_SIZE (2 * SIZE_T_SIZE)
    if (GET(HDRP(heap_listp)) != PACK(PROLOGUE_SIZE, 0x1))
    {
        dbg_printf("%s-%s-%d\n", __FILE__, __func__, __LINE__);
        exit(127);
    }
    if (GET(FTRP(heap_listp)) != PACK(PROLOGUE_SIZE, 0x1))
    {
        dbg_printf("%s-%s-%d\n", __FILE__, __func__, __LINE__);
        exit(127);
    }

    //检查堆的边界
    if (heap_listp < (char *)mem_heap_lo())
    {
        dbg_printf("%s-%s-%d\n", __FILE__, __func__, __LINE__);
        exit(127);
    }

    // 不清楚为什么 mem_heap_hi() 的实现减去了 1
    if (bp > (char *)mem_heap_hi() + 1)
    {
        dbg_printf("%s-%s-%d\n", __FILE__, __func__, __LINE__);
        exit(127);
    }

    /* checking the free list */
    // pred/succ 是连续的， A's next is B, then B's pred must be A
    // 分离空闲链表中，各个 free block size 在该链表的范围之内
    size_t *entry_listp = segregated_free_listp;
    // 外循环遍历分离空闲链表的所有入口
    while (entry_listp < segregated_free_listp + SEGREGATED_FREE_LIST_ENTRY_SIZE)
    {
        // 内循环遍历单个空闲链表
        char *pred = (char *)entry_listp;
        char *succ = SUCC_BLKP(pred);
        while (succ != NULL)
        {
            size_t size = GET_SIZE(HDRP(succ));
            if (find_entry_in_segregated_list(size) != entry_listp)
            {
                dbg_printf("%s-%s-%d\n", __FILE__, __func__, __LINE__);
                exit(127);
            }

            if (PRED_BLKP(succ) != pred)
            {
                dbg_printf("%s-%s-%d\n", __FILE__, __func__, __LINE__);
                exit(127);
            }

            // 空闲链表中不应该出现已分配 block
            if (GET_ALLOC(HDRP(succ)))
            {
                dbg_printf("%s-%s-%d\n", __FILE__, __func__, __LINE__);
                exit(127);
            }
            else
            {
                free_block_num--;
            }

            // 所有的空闲链表都在 mem_heap_lo() 和 mem_heap_hi() 之间
            if (succ < (char *)mem_heap_lo() || succ > (char *)mem_heap_hi())
            {
                dbg_printf("%s-%s-%d\n", __FILE__, __func__, __LINE__);
                exit(127);
            }

            // 开始下一个节点的检查
            pred = succ;
            succ = SUCC_BLKP(succ);
        }

        entry_listp += SEGREGATED_FREE_LIST_ENTRY_STEP;
    }

    // 通过 header footer 计算 free block 的个数，等于通过 pred succ 得到的个数
    if (free_block_num != 0)
    {
        dbg_printf("%s-%s-%d\n", __FILE__, __func__, __LINE__);
        exit(127);
    }
}
