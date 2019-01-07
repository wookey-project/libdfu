#ifndef _USB_DFU_UTILS_H
#define _USB_DFU_UTILS_H

#include "api/types.h"
#include "api/print.h"
#include "api/regutils.h"
#include "usb.h"
/* usb driver control header */
#include "usb_control.h"

#define MAX_DFU_CMD_QUEUE_SIZE 8

typedef enum dfu_status_enum {
    OK              = 0x00,
    ERRTARGET       = 0x01,
    ERRFILE         = 0x02,
    ERRWRITE        = 0x03,
    ERRERASE        = 0x04,
    ERRCHECK_ERASED	= 0x05,
    ERRPROG         = 0x06,
    ERRVERIFY       = 0x07,
    ERRADDRESS      = 0x08,
    ERRNOTDONE      = 0x09,
    ERRFIRMWARE     = 0x0A,
    ERRVENDOR       = 0x0B,
    ERRUSBR         = 0x0C,
    ERRPOR          = 0x0D,
    ERRUNKNOWN      = 0x0E,
    ERRSTALLEDPKT   = 0x0F,
} dfu_status_enum_t;

void dfu_leave_session_with_error(const dfu_status_enum_t new_status);

/*
 * Task callback, executed at the end of a data transfer reception,
 * to decide what to do with these data.
 * @param datat     he buffer address on which the data should be written from,
 *                  to the storage backend
 * @param data_size the amount of data to write
 * @param blocknum  the current chunk number, given by the host
 */
typedef uint8_t (*dfu_write_block_cb_t)(uint8_t ** volatile data, uint16_t size, uint16_t blocknum);

/*
 * Task callback, executed at the begining of a data upload request
 * to ask the uper layer how to get back the data into the DFU buffer
 * before transmission
 */
typedef uint8_t (*dfu_read_block_cb_t)(uint8_t *data, uint16_t size);

typedef void (*dfu_eof_cb_t)(void);

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
 * @param eof_cb   the callback executed when the download (or upload) session
 *                 has terminated without error.
 * @param buffer   the data buffer to use for storing data from/to USB FIFO
 * @param max_size the buffer size, at least 64, must be a power of 2.
 */
void dfu_init(dfu_write_block_cb_t write_cb,
              dfu_read_block_cb_t  read_cb,
              dfu_eof_cb_t         eof_cb,
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
void dfu_load_finished(uint16_t bytes_read);

#endif
