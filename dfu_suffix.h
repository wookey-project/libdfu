#ifndef DFU_SUFFIX_H
#define DFU_SUFFIX_H

typedef struct dfu_suffix {
    uint32_t dwCRC;
    unsigned char suffixlen;
    uint16_t bcdDFU;
    uint16_t idVendor;
    uint16_t idProduct;
    uint16_t bcdDevice;
} dfu_suffix_t ;

int parse_dfu_suffix(struct dfu_file *file);

#endif /* DFU_SUFFIX_H */
