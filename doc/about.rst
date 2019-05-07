Overview
--------

Principles
""""""""""

The DFU (Device Firmware Update) is a USB class defined by the USB consortium
in order to define a vendor-independent, device-independent mechanism to update
USB devices.

The DFU protocol can be seen as a communication media to download or upload
firmwares from/to a device.

.. caution::
   The DFU protocol is not responsible for the firmware image security
   (integrity, authenticity and so on)

The DFU protocol is based on a relatively big state automaton defined in the
`USB DFU class description
<http://www.usb.org/developers/docs/devclass_docs/DFU_1.1.pdf>`_

Limitations
"""""""""""

The DFU protocol only maintain a connected channel between the host and the
device through which they can exchange data.

The channel is **not** secured, not authenticated at DFU stack level.

The DFU protocol is using the control endpoint to communicate, without
requiring a dedicated endpoint to transmit or receive data. As a consequence,
the USB URB (USB data blocks) size are limited by the control endpoint specific
constraints.

This endpoint also manage the control part of the protocol.

