The DFU stack
=============

The LibDFU project aim to implement a complete USB DFU (Direct Firmware Update)
device-side automaton.

This automaton should permit to any device to support both DFU upload and download
modes.
This stack does not aim to implement the USB control stack or the USB driver, and request
these two components to exists. The current implementation of libDFU is compatible with the
Wookey STM32F439 driver API, and should be easily portable with other drivers.

.. toctree::
   :caption: Table of Contents
   :name: mastertoc
   :maxdepth: 2

   About the DFU protocol <about>
   The DFU API <api>
   FAQ <faq>


