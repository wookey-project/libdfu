#ifndef USB_DFU_PRIV_H_
#define USB_DFU_PRIV_H_

#include "api/dfu.h"

#define MAX_DFU_CMD_QUEUE_SIZE 8

typedef struct __packed dfu_functional_descriptor {
	uint8_t bLength;
	uint8_t bDescriptorType;
	struct {
		uint8_t bitCanDnload:1;
		uint8_t bitCanUpload:1;
		uint8_t bitManifestationTolerant:1;
		uint8_t bitWillDetach:1;
		uint8_t reserved:4;
	} bmAttributes;
	uint16_t wDetachTimeOut;
	uint16_t wTransferSize;
	uint16_t bcdDFUVersion;
} dfu_functional_descriptor_t;


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

#define DFU_QUEUE_MAX_SIZE 10
#define DFU_DATA_QUEUE_MAX_SIZE 10
#define MAX_POLL_TIMEOUT 50

typedef enum dfu_request {
 USB_RQST_DFU_DETACH             =  0x00,
 USB_RQST_DFU_DNLOAD             =  0x01,
 USB_RQST_DFU_UPLOAD             =  0x02,
 USB_RQST_DFU_GET_STATUS         =  0x03,
 USB_RQST_DFU_CLEAR_STATUS       =  0x04,
 USB_RQST_DFU_GET_STATE          =  0x05,
 USB_RQST_DFU_ABORT              =  0x06
} dfu_request_t;

#define USB_RQST_DFU_DEBUG_CHKSIGN               0xF0
#define USB_RQST_DFU_DEBUG_DECRYPT               0xF1
#define USB_RQST_DFU_DEBUG_CRYPT                 0xF2
#define USB_RQST_DFU_DEBUG_SETADDR               0xF3
#define USB_RQST_DFU_DEBUG_GETADDR               0xF4
#define USB_RQST_DFU_DEBUG_SETSIZE               0xF5
#define USB_RQST_DFU_DEBUG_GETSIZE               0xF6




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

typedef enum dfu_state_enum {
    APPIDLE                 = 0x00,
    APPDETACH               = 0x01,
    DFUIDLE                 = 0x02,
    DFUDNLOAD_SYNC          = 0x03,
    DFUDNBUSY               = 0x04,
    DFUDNLOAD_IDLE          = 0x05,
    DFUMANIFEST_SYNC        = 0x06,
    DFUMANIFEST             = 0x07,
    DFUMANIFEST_WAIT_RESET  = 0x08,
    DFUUPLOAD_IDLE          = 0x09,
    DFUERROR                = 0x0A,
}dfu_state_enum_t;


typedef struct __packed {
    uint8_t bStatus;
    uint8_t bwPollTimeout[3];
    uint8_t bState;
    uint8_t iString;
} device_dfu_status_t;

/*
 * DFU context
 * TODO: fields should be ordered more cleanly, depending on their:
 * 1) usage
 * 2) size per usage
 * for a better readability
 */
typedef struct  {
    uint8_t               block_in_progress;
    uint8_t               session_in_progress;
    dfu_state_enum_t      state;
    dfu_status_enum_t     status;
    int8_t                data_out_nb_blocks;
    int32_t               data_out_length;
    int8_t                data_in_nb_blocks;
    int32_t               data_in_length;
    uint32_t              flash_address;
    int16_t               detach_timeout_ms;
    uint64_t              detach_timeout_start;
    uint16_t              poll_timeout_ms;
    uint64_t              poll_start;
    int16_t               block_size;
    uint16_t              transfert_size;
    int32_t               firmware_size;
    uint8_t **            data_out_buffer;
    uint8_t **            data_in_buffer;
    uint16_t              data_out_current_block_nb;
    uint16_t              data_in_current_block_nb;
    uint32_t              current_block_offset;
    dfu_read_block_cb_t   cb_read;
    dfu_write_block_cb_t  cb_write;
    bool                  data_to_store;
    bool                  data_to_load;
    //uint32_t data_out_buffer_index;
    //uint32_t data_in_buffer_index;
} dfu_context_t;

void dfu_init_context(void);

#endif/*USB_DFU_PRIV_H_*/
