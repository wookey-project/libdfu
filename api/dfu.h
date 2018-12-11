#ifndef _USB_DFU_UTILS_H
#define _USB_DFU_UTILS_H

#include "api/types.h"
#include "api/print.h"
#include "api/regutils.h"
#include "usb.h"
/* usb driver control header */
#include "usb_control.h"

#define MAX_DFU_CMD_QUEUE_SIZE 8

/*
 * Task callback, executed at the end of a data transfer reception,
 * to decide what to do with these data.
 */
typedef uint8_t (*dfu_write_block_cb_t)(uint8_t ** volatile data, uint16_t size);

/*
 * Task callback, executed at the begining of a data upload request
 * to ask the uper layer how to get back the data into the DFU buffer
 * before transmission
 */
typedef uint8_t (*dfu_read_block_cb_t)(uint8_t *data, uint16_t size);


/*
 * Early initialization, declaring the DFU stack. This include the USB
 * stack initialisation. This function must be called before the 
 * sys_init(INIT_DONE) call.
 * Request PERM_RES_DEV_BUSES permission.
 * CAUTION: in USB-HS mode, the task must have the MAP_VOLUNTARY permission
 */
void dfu_early_init(void);

/**
 * @brief initialize the DFU stack
 *
 * @param write_cb the callback executed when an input buffer is ready to be
 *                 stored
 * @param read_cb  the callback executed when an input data is requested from
 *                 the DFU stack (in upload mode)
 * @param buffer   the data buffer to use for storing data from/to USB FIFO
 * @param max_size the buffer size, at least 64, must be a power of 2.
 */
void dfu_init(dfu_write_block_cb_t write_cb,
              dfu_read_block_cb_t  read_cb,
              uint8_t **buffer,
              uint16_t max_size);

/**
 * Run the DFU automaton.
 * This is *not* a loop, as the task may require to support, in the same loop,
 * external events, such as IPC. The task has to handle the loop, using a
 * block such as:
 * while (1) {
 *   dfu_exec_automaton();
 *   if (sys_ipc(IPC_RECV_ASYNC, &id, &buf) == SYS_E_DONE) {
 *     // handle IPC request
 *   }
 * }
 */
void dfu_exec_automaton(void);

/*
 * The storing backend has finished to store data ? This function inform the
 * DFU that it can leave the DNLOAD_SYNC/DNBUSY couple.
 */
void dfu_store_finished(void);

/*
 * The loading backend has finished to load data ? This function inform the
 * DFU that it can send the buffer content into the USB device output FIFO
 */
void dfu_load_finished(void);

#endif
