%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module contains functions that determine how recoverable faults encountered by user-level threads are propagated to the appropriate fault handlers.

> module SEL4.Kernel.FaultHandler (handleFault, isValidFaultHandler) where

\begin{impdetails}

% {-# BOOT-IMPORTS: SEL4.Machine SEL4.Model SEL4.Object.Structures SEL4.API.Failures #-}
% {-# BOOT-EXPORTS: handleFault isValidFaultHandler #-}

> import SEL4.API.Failures
> import SEL4.Machine
> import SEL4.Model
> import SEL4.Object
> import SEL4.Object.Structures(TCB(..), CTE(..))
> import SEL4.Kernel.Thread
> import SEL4.Kernel.CSpace

\end{impdetails}

> isValidFaultHandler :: Capability -> Bool
> isValidFaultHandler cap =
>     case cap of
>         EndpointCap { capEPCanSend = True } -> capEPCanGrant cap || capEPCanGrantReply cap
>         NullCap -> True
>         _ -> False

\subsection{Handling Faults}

Faults generated by the "handleEvent" function (which is defined in \autoref{sec:api.syscall}) are caught and sent to "handleFault", defined below.

The parameters of this function are the fault and a pointer to the thread which requested the kernel operation that generated the fault.

> handleFault :: PPtr TCB -> Fault -> Kernel ()

When a thread faults, the kernel attempts to send a fault IPC to the fault handler endpoint. This has the side-effect of suspending the thread, placing it in the "BlockedOnFault" state until the recipient of the fault IPC replies to it. If the IPC fails, we call "handleDoubleFault" instead.

> handleFault tptr ex = do
>     tcb <- getObject tptr
>     hasFh <- sendFaultIPC tptr (cteCap (tcbFaultHandler tcb)) ex `catchFailure` const (return False)
>     unless hasFh $ handleNoFaultHandler tptr

\subsection{Sending Fault IPC}

If a thread causes a fault, then an IPC containing details of the fault is sent to a fault handler endpoint specified in the thread's TCB.

> sendFaultIPC :: PPtr TCB -> Capability -> Fault -> KernelF Fault Bool
> sendFaultIPC tptr handlerCap fault = do

>     case handlerCap of

The kernel stores a copy of the fault in the thread's TCB, and performs an IPC send operation to the fault handler endpoint on behalf of the faulting thread. When the IPC completes, the fault will be retrieved from the TCB and sent instead of the message registers.

>         EndpointCap { capEPCanGrant = canGrant, capEPCanGrantReply = canGrantReply } ->
>           withoutFailure $ do
>             threadSet (\tcb -> tcb {tcbFault = Just fault}) tptr
>             sendIPC True True (capEPBadge handlerCap)
>                 canGrant canGrantReply tptr (capEPPtr handlerCap)
>             return True
>         NullCap -> withoutFailure $ return False
>         _ -> fail "must be send+grant EPCap or NullCap"

\subsection{Double Faults}

> handleNoFaultHandler :: PPtr TCB -> Kernel ()

If a fault IPC cannot be sent because the fault handler endpoint capability is missing, then we are left with two faults which cannot be reasonably handled. The faults are both printed to the console for debugging purposes. The faulting thread is placed in the "Inactive" state, which will prevent it running until it is explicitly restarted.

> handleNoFaultHandler tptr = do
>         setThreadState Inactive tptr

