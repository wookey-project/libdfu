/** @file usb_device.h
 * \brief Contains usb descriptors
 */
#ifndef _USB_DEVICE_H
#define _USB_DEVICE_H

/* Strings */
#define MAX_DESC_STRING_SIZE		32
#define LANGUAGE_ENGLISH		0x0409

#define STRING_MANUFACTURER		"ANSSI"
#define STRING_MANUFACTURER_INDEX	1
#define STRING_PRODUCT			"goodusb"
#define STRING_PRODUCT_INDEX		2
#define STRING_SERIAL			"123456789012345678901234"
#define STRING_SERIAL_INDEX		3

#define ID_VENDOR           0xDEAD
#define ID_PRODUCT          0xCAFE

#endif
