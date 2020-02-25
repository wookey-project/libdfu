/*
 *
 * Copyright 2018 The wookey project team <wookey@ssi.gouv.fr>
 *   - Ryad     Benadjila
 *   - Arnauld  Michelizza
 *   - Mathieu  Renard
 *   - Philippe Thierry
 *   - Philippe Trebuchet
 *
 * This package is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * the Free Software Foundation; either version 2.1 of the License, or (at
 * ur option) any later version.
 *
 * This package is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
 * PARTICULAR PURPOSE. See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along
 * with this package; if not, write to the Free Software Foundation, Inc., 51
 * Franklin St, Fifth Floor, Boston, MA 02110-1301 USA
 *
 */
#ifndef USB_DFU_PRIV_H_
#define USB_DFU_PRIV_H_

#include "api/dfu.h"

#define MAX_TIME_DETACH     4000




typedef struct __packed {
        uint32_t magic;
        uint32_t type;
        uint32_t version;
        uint32_t len;
        uint32_t siglen;
} dfu_sec_metadata_hdr_t;


typedef struct __packed {
        uint16_t bcdDevice;
        uint16_t idProduct;
        uint16_t idVendor;
        uint16_t bcdDFU;
        uint8_t ucDfuSignature[3];
        uint8_t bLength;
        uint32_t dwCRC;
} dfu_suffix_t;

typedef enum dfu_request {
 USB_RQST_DFU_DETACH            =  0x00,
 USB_RQST_DFU_DNLOAD            =  0x01,
 USB_RQST_DFU_UPLOAD            =  0x02,
 USB_RQST_DFU_GET_STATUS        =  0x03,
 USB_RQST_DFU_CLEAR_STATUS      =  0x04,
 USB_RQST_DFU_GET_STATE         =  0x05,
 USB_RQST_DFU_ABORT             =  0x06
} dfu_request_t;

typedef enum dfu_state_enum {
    APPIDLE                	= 0x00,
    APPDETACH               	= 0x01,
    DFUIDLE                 	= 0x02,
    DFUDNLOAD_SYNC          	= 0x03,
    DFUDNBUSY               	= 0x04,
    DFUDNLOAD_IDLE          	= 0x05,
    DFUMANIFEST_SYNC        	= 0x06,
    DFUMANIFEST             	= 0x07,
    DFUMANIFEST_WAIT_RESET  	= 0x08,
    DFUUPLOAD_IDLE          	= 0x09,
    DFUERROR                	= 0x0A,
}dfu_state_enum_t;


typedef struct __packed {
    uint8_t bStatus;
    uint8_t bwPollTimeout[3];
    uint8_t bState;
    uint8_t iString;
} device_dfu_status_t;



#endif/*USB_DFU_PRIV_H_*/
