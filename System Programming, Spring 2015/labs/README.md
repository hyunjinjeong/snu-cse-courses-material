# Labs

## 1. Buffer Overflow

In Buffer Overflow Lab, you will develop a detailed understanding of IA-32 calling conventions and stack organization. It involves applying a series of buffer overflow attacks on an executable file bufbomb in the lab directory.

## 2. Kernel Driver

A module is pieces of code that can be loaded and unloaded into the kernel upon demand. Modules can use privileged instructions without system calls, because a kernel module is loaded and executed within a kernel.

Device Drivers is one kind of kernel module, which provides the means to communicate with the (virtual / real) hardware.

In this lab, there will be two parts:

1. Implement a kernel module that outputs the list of all parent processes up to the root when called through ioctl().
2. Implement a kernel module to manage the processor’s Performance Monitoring Unit (PMU).

## 3. Malloc

In this lab you will be writing a dynamic storage allocator for C programs, i.e., your own version of the malloc, free and realloc routines. You are encouraged to explore the design space creatively and implement an allocator that is correct, efficient and fast.

## 4. Shell

The purpose of this lab is to become more familiar with the concepts of process control and signalling. You’ll do this by writing a simple Unix shell program that supports job control.

## 5. Proxy

An echo proxy is a program that acts as a middleman between an echo client and an echo server. Instead of contacting the echo server directly, the client contacts the proxy, which forwards the request on to the end echo server. When the echo server replies to the proxy, the proxy sends the reply on to the client.

In this lab, there are two parts: a simple sequential proxy and a concurrent echo proxy.

1. In the first part of the lab, you will write a simple sequential proxy that repeatedly waits for a request, forwards the request to the echo server, and returns the result back to the client, keeping a log of such requests in a disk file. This part will give you some experience with network programming.
2. In the second part of the lab, you will upgrade your proxy so that it uses threads to deal with multiple clients concurrently. This part will give you some experience with concurrency and synchronization, which are crucial computer systems concepts.
