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



void dfu_early_init(void);

void dfu_init(dfu_write_block_cb_t write_cb,
              dfu_read_block_cb_t  read_cb);

void dfu_early_init(void);

void dfu_loop(void);


#endif
