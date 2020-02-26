%
% Copyright 2014, General Dynamics C4 Systems
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
%

This module specifies the behavior of schedule context objects.

\begin{impdetails}

This module uses the C preprocessor to select a target architecture.

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.Object.SchedContext (
>         schedContextUnbindAllTCBs, invokeSchedContext,
>         invokeSchedControlConfigure, getSchedContext,
>         schedContextUnbindTCB, schedContextBindTCB, schedContextResume,
>         setSchedContext, updateTimeStamp, commitTime, rollbackTime,
>         refillHd, refillTl, minBudget, minBudgetUs, refillCapacity, refillBudgetCheck,
>         refillSplitCheck, isCurDomainExpired, refillUnblockCheck,
>         refillReady, tcbReleaseEnqueue, tcbReleaseDequeue, refillSufficient, postpone,
>         schedContextDonate, maybeDonateSc, maybeReturnSc, schedContextUnbindNtfn,
>         schedContextMaybeUnbindNtfn, isRoundRobin, getRefills, setRefills, refillFull,
>         schedContextCompleteYieldTo, schedContextCancelYieldTo, refillAbsoluteMax,
>         schedContextUpdateConsumed, scRefillTail, scReleased, setConsumed
>     ) where

\begin{impdetails}

> import Prelude hiding (Word)
> import SEL4.Config
> import SEL4.Machine.Hardware
> import SEL4.Machine.RegisterSet(PPtr(..), Word)
> import SEL4.API.Failures(SyscallError(..))
> import SEL4.API.Types(MessageInfo(..))
> import {-# SOURCE #-} SEL4.Kernel.VSpace(lookupIPCBuffer)
> import SEL4.Model.Failures
> import SEL4.Model.Preemption(KernelP, withoutPreemption)
> import SEL4.Model.PSpace(getObject, setObject)
> import SEL4.Model.StateData
> import {-# SOURCE #-} SEL4.Object.Notification
> import {-# SOURCE #-} SEL4.Object.Reply
> import SEL4.Object.Structures
> import {-# SOURCE #-} SEL4.Object.TCB(threadGet, threadSet, checkBudget, chargeBudget, replaceAt, setTimeArg, setMessageInfo, setMRs)
> import {-# SOURCE #-} SEL4.Kernel.Thread
> import SEL4.API.Invocation(SchedContextInvocation(..), SchedControlInvocation(..))

> import Data.Bits
> import Data.List(delete)
> import Data.Word(Word64)
> import Data.Maybe

\end{impdetails}

> minBudget :: Word64
> minBudget = 2 * kernelWCETTicks

> minBudgetUs :: Word64
> minBudgetUs = 2 * kernelWCET_us

> coreSchedContextBytes :: Int
> coreSchedContextBytes = 88

> refillSizeBytes :: Int
> refillSizeBytes = 16

> getSchedContext :: PPtr SchedContext -> Kernel SchedContext
> getSchedContext = getObject

> setSchedContext :: PPtr SchedContext -> SchedContext -> Kernel ()
> setSchedContext = setObject

> refillHd :: SchedContext -> Refill
> refillHd sc = scRefills sc !! scRefillHead sc

> updateList :: Int -> a -> [a] -> [a]
> updateList n x xs = take n xs ++ [x] ++ drop (n + 1) xs

> setRefillHd :: PPtr SchedContext -> Refill -> Kernel ()
> setRefillHd scPtr new = do
>     sc <- getSchedContext scPtr
>     let refills = scRefills sc
>     let idx = scRefillHead sc
>     let sc' = sc { scRefills = replaceAt idx refills new }
>     setSchedContext scPtr sc'

> scRefillTail :: SchedContext -> Int
> scRefillTail sc = (scRefillHead sc + scRefillCount sc - 1) `mod` scRefillMax sc

> scActive :: PPtr SchedContext -> Kernel Bool
> scActive scPtr = do
>     sc <- getSchedContext scPtr
>     return $ scRefillMax sc > 0

> scReleased :: PPtr SchedContext -> Kernel Bool
> scReleased scPtr = do
>     active <- scActive scPtr
>     if active
>       then refillReady scPtr
>       else return False

> refillTl :: SchedContext -> Refill
> refillTl sc = scRefills sc !! scRefillTail sc

> setRefillTl :: PPtr SchedContext -> Refill -> Kernel ()
> setRefillTl scPtr new = do
>     sc <- getSchedContext scPtr
>     let refills = scRefills sc
>     let idx = scRefillTail sc
>     let sc' = sc { scRefills = replaceAt idx refills new }
>     setSchedContext scPtr sc'

> setRefills :: PPtr SchedContext -> [Refill] -> Kernel ()
> setRefills scPtr refills = do
>     sc <- getSchedContext scPtr
>     setSchedContext scPtr (sc { scRefills = refills })

> getRefills :: PPtr SchedContext -> Kernel [Refill]
> getRefills scPtr = do
>     sc <- getSchedContext scPtr
>     return $ scRefills sc

> refillSingle :: PPtr SchedContext -> Kernel Bool
> refillSingle scPtr = do
>     sc <- getSchedContext scPtr
>     return $ scRefillHead sc == scRefillTail sc

> refillFull :: PPtr SchedContext -> Kernel Bool
> refillFull scPtr = do
>     sc <- getSchedContext scPtr
>     sz <- refillSize scPtr
>     return $ sz == scRefillMax sc

> refillEmpty :: PPtr SchedContext -> Kernel Bool
> refillEmpty scPtr = do
>     sc <- getSchedContext scPtr
>     return $ scRefillMax sc == 0

> liftScPtr :: PPtr SchedContext -> (SchedContext -> a) -> Kernel a
> liftScPtr scPtr f = do
>     sc <- getSchedContext scPtr
>     return $ f sc

> refillNext :: PPtr SchedContext -> Int -> Kernel Int
> refillNext scPtr index = do
>     sc <- getSchedContext scPtr
>     return $ if (index == scRefillMax sc - 1) then 0 else index + 1

> -- Odd argument order plays well with `liftScPtr`.
> refillIndex :: Int -> SchedContext -> Refill
> refillIndex index sc = scRefills sc !! index

> refillSize :: PPtr SchedContext -> Kernel Int
> refillSize scPtr = do
>     sc <- getSchedContext scPtr
>     if scRefillHead sc <= scRefillTail sc
>         then return $ scRefillTail sc - scRefillHead sc + 1
>         else return $ scRefillTail sc + 1 + (scRefillMax sc - scRefillHead sc)

> refillsCapacity :: Ticks -> [Refill] -> Int -> Ticks
> refillsCapacity usage refills headIndex =
>     if rAmount (refills !! headIndex) < usage
>         then 0
>         else rAmount (refills !! headIndex) - usage

> refillCapacity :: PPtr SchedContext -> Ticks -> Kernel Ticks
> refillCapacity scPtr usage = do
>     refills <- getRefills scPtr
>     sc <- getSchedContext scPtr
>     return $ refillsCapacity usage refills (scRefillHead sc)

> sufficientRefills :: Ticks -> [Refill] -> Int -> Bool
> sufficientRefills usage refills headIndex = minBudget <= refillsCapacity usage refills headIndex

> refillSufficient :: PPtr SchedContext -> Ticks -> Kernel Bool
> refillSufficient scPtr usage = do
>     refills <- getRefills scPtr
>     sc <- getSchedContext scPtr
>     return $ sufficientRefills usage refills (scRefillHead sc)

> refillPopHead :: PPtr SchedContext -> Kernel Refill
> refillPopHead scPtr = do
>     isSingle <- refillSingle scPtr
>     assert (not isSingle) "queues cannot be smaller than 1"
>     sc <- getSchedContext scPtr
>     refill <- return $ refillHd sc
>     nextRefill <- refillNext scPtr (scRefillHead sc)
>     setSchedContext scPtr (sc { scRefillHead = nextRefill })
>     return refill

> refillAddTail :: PPtr SchedContext -> Refill -> Kernel ()
> refillAddTail scPtr refill = do
>     sc <- getSchedContext scPtr
>     sz <- refillSize scPtr
>     assert (sz < scRefillMax sc) "cannot add beyond queue size"
>     newTail <- refillNext scPtr (scRefillTail sc)
>     refills <- return $ replaceAt newTail (scRefills sc) refill
>     setSchedContext scPtr (sc { scRefills = refills, scRefillCount = sz + 1 })

> maybeAddEmptyTail :: PPtr SchedContext -> Kernel ()
> maybeAddEmptyTail scPtr = do
>     robin <- isRoundRobin scPtr
>     when robin $ do
>         curTime <- getCurTime
>         refillAddTail scPtr (Refill { rTime = curTime, rAmount = 0 })

> refillNew :: PPtr SchedContext -> Int -> Ticks -> Ticks -> Kernel ()
> refillNew scPtr maxRefills budget period = do
>     sc <- getSchedContext scPtr
>     assert (minBudget < budget) "budget must be greater than the minimum"
>     curTime <- getCurTime
>     refills <- getRefills scPtr
>     refills' <- return $ replaceAt 0 refills (Refill { rTime = curTime, rAmount = budget })
>     sc' <- return $ sc { scPeriod = period,
>                          scRefills = refills',
>                          scRefillMax = maxRefills,
>                          scRefillHead = 0,
>                          scRefillCount = 1 }
>     setSchedContext scPtr sc'
>     maybeAddEmptyTail scPtr

> refillReady :: PPtr SchedContext -> Kernel Bool
> refillReady scPtr = do
>     curTime <- getCurTime
>     sc <- getSchedContext scPtr
>     return $ rTime (refillHd sc) <= curTime + kernelWCETTicks

> refillUpdate :: PPtr SchedContext -> Ticks -> Ticks -> Int -> Kernel ()
> refillUpdate scPtr newPeriod newBudget newMaxRefills = do
>     sc <- getSchedContext scPtr
>     assert (scRefillMax sc > 0) "refill must be initialised in order to be updated"
>     refills <- getRefills scPtr
>     refills1 <- return $ replaceAt 0 refills (refills !! (scRefillHead sc))
>     sc1 <- return $ sc { scPeriod = newPeriod,
>                          scRefills = refills1,
>                          scRefillMax = newMaxRefills,
>                          scRefillHead = 0,
>                          scRefillCount = 1 }
>     setSchedContext scPtr sc1
>     curTime <- getCurTime
>     ready <- refillReady scPtr
>     refills2 <- if ready then return $ replaceAt 0 refills1 ((head refills1) { rTime = curTime })
>                 else return refills1
>     setRefills scPtr refills2
>     if (rAmount (head refills2) >= newBudget)
>         then do
>             refills3 <- return $ replaceAt 0 refills2 ((head refills2) { rAmount = newBudget })
>             setRefills scPtr refills3
>             maybeAddEmptyTail scPtr
>         else refillAddTail scPtr (Refill { rTime = rTime (head refills2) + newPeriod,
>                                             rAmount = (newBudget - rAmount (head refills2)) })

> scheduleUsed :: PPtr SchedContext -> Refill -> Kernel ()
> scheduleUsed scPtr new = do
>     sc <- getSchedContext scPtr
>     empty <- refillEmpty scPtr
>     if empty
>       then do
>         assert (rAmount new >= minBudget) "Refill doesn't have enough budget"
>         refillAddTail scPtr new
>       else do
>         assert (rTime new >= rTime (refillTl sc) + rAmount (refillTl sc))
>             "The refills being disjoint allows for them to be merged with the resulting refill being earlier"
>         full <- refillFull scPtr
>         if (rAmount new < minBudget
>               && not full
>               && rAmount (refillTl sc) + rAmount new >= 2 * minBudget)
>           then do
>             let remainder = minBudget - rAmount new
>             let new' = new { rTime = rTime new - remainder,
>                              rAmount = rAmount new + remainder }
>             let tl = refillTl sc
>             let tl' = tl { rAmount = rAmount tl - remainder }
>             setRefillTl scPtr tl'
>             refillAddTail scPtr new'
>           else if (rAmount new < minBudget || full) then do
>             let tl = refillTl sc
>             let tl' = tl { rTime = rTime new - rAmount tl,
>                            rAmount = rAmount tl + rAmount new }
>             setRefillTl scPtr tl'
>           else do
>             refillAddTail scPtr new
>     empty' <- refillEmpty scPtr
>     assert (not empty) "We just inserted something to the refills, it better not be empty!"

> refillBudgetCheck :: Ticks -> Kernel ()
> refillBudgetCheck usage = do
>     scPtr <- getCurSc
>     sc <- getSchedContext scPtr
>     let last_entry = rTime (refillHd sc)
>     let used = Refill { rTime = last_entry + scPeriod sc,
>                         rAmount = usage }
>     ready <- refillReady scPtr
>     used' <- if (not ready || rAmount (refillHd sc) < usage)
>       then do
>         setSchedContext scPtr (sc { scRefillCount = 0 })
>         return $ Refill { rTime = rTime used + usage,
>                           rAmount = scBudget sc }
>       else if (usage == rAmount (refillHd sc))
>         then do
>           refillPopHead scPtr
>           return used
>         else do
>           let remnant = rAmount (refillHd sc) - usage
>           if remnant >= minBudget
>             then do
>               setRefillHd scPtr (Refill { rTime = rTime (refillHd sc) + usage,
>                                           rAmount = remnant })
>               return used
>             else do
>               refillPopHead scPtr
>               empty <- refillEmpty scPtr
>               if empty
>                 then do
>                   return $ Refill { rTime = rTime used - remnant,
>                                   rAmount = rAmount used + remnant }
>                 else do
>                   head <- liftScPtr scPtr refillHd
>                   setRefillHd scPtr (Refill { rTime = rTime head - remnant,
>                                               rAmount = rAmount head + remnant })
>                   return used
>     scheduleUsed scPtr used'

> refillSplitCheck :: PPtr SchedContext -> Time -> Kernel ()
> refillSplitCheck scPtr usage = do
>     scPtr <- getCurSc
>     sc <- getSchedContext scPtr
>     rfillhd <- return $ refillHd sc
>     assert (usage > 0) "something is seriously wrong if this is called and no time has been used"
>     assert (usage <= rAmount rfillhd) "Time usage must be within (0, rAmount of the refills head]"
>     assert (scPeriod sc > 0) "period should be greater than 0"
>     remnant <- return $ rAmount rfillhd - usage
>     new <- return (Refill { rTime = rTime rfillhd + scPeriod sc, rAmount = usage })
>     size <- refillSize scPtr
>     if size == scRefillMax sc || remnant < minBudget
>         then do
>             single <- refillSingle scPtr
>             if single
>                 then setRefills scPtr $ replaceAt (scRefillHead sc) (scRefills sc) (new { rAmount = rAmount new + remnant })
>                 else do
>                     r <- refillPopHead scPtr
>                     sc' <- getSchedContext scPtr
>                     hdRefill <- return $ refillHd sc'
>                     setRefills scPtr $ replaceAt (scRefillHead sc') (scRefills sc') (hdRefill { rAmount = rAmount hdRefill + remnant })
>                     scheduleUsed scPtr new
>         else do
>             assert (remnant >= minBudget) "leave remnant as reduced replenishment"
>             hdRefill <- return $ refillHd sc
>             setRefills scPtr $ replaceAt (scRefillHead sc) (scRefills sc) (hdRefill { rAmount = remnant })
>             scheduleUsed scPtr new

> refillUnblockCheckMergable :: PPtr SchedContext -> Kernel Bool
> refillUnblockCheckMergable scPtr = do
>     head <- liftScPtr scPtr refillHd
>     let amount = rAmount head
>     let tail = rTime head + amount
>     headIndex <- liftScPtr scPtr scRefillHead
>     nextRefillIndex <- refillNext scPtr headIndex
>     nextRefill <- liftScPtr scPtr (refillIndex nextRefillIndex)
>     let enough_time = rTime nextRefill <= tail
>     refills <- refillSize scPtr
>     return (refills > 1 && enough_time)

> refillUnblockCheck :: PPtr SchedContext -> Kernel ()
> refillUnblockCheck scPtr = do
>     ifM (isRoundRobin scPtr)
>       (do
>         curTime <- getCurTime
>         head <- liftScPtr scPtr refillHd
>         setRefillHd scPtr $ head { rTime = curTime + kernelWCETTicks }
>         refillCount <- liftScPtr scPtr scRefillCount
>         when (refillCount > 1) $ do
>           head <- liftScPtr scPtr refillHd
>           tail <- liftScPtr scPtr refillTl
>           setRefillTl scPtr $ tail { rTime = rTime head + rAmount head })
>       (whenM (refillReady scPtr) $ do
>         setReprogramTimer True
>         curTime <- getCurTime
>         head <- liftScPtr scPtr refillHd
>         setRefillHd scPtr $ head { rTime = curTime + kernelWCETTicks }
>         whenM (refillUnblockCheckMergable scPtr) $ do
>           amount <- liftM rAmount $ liftScPtr scPtr refillHd
>           refillPopHead scPtr
>           curTime <- getCurTime
>           head <- liftScPtr scPtr refillHd
>           setRefillHd scPtr $ Refill { rTime = curTime + kernelWCETTicks,
>                                        rAmount = rAmount head + amount })

> schedContextUpdateConsumed :: PPtr SchedContext -> Kernel Time
> schedContextUpdateConsumed scPtr = do
>     sc <- getSchedContext scPtr
>     consumed <- return $ scConsumed sc
>     if consumed >= maxTicksToUs
>         then do
>             setSchedContext scPtr $ sc { scConsumed = scConsumed sc - maxTicksToUs }
>             return maxTicksToUs
>         else do
>             setSchedContext scPtr $ sc { scConsumed = 0 }
>             return $ ticksToUs consumed

> setConsumed :: PPtr SchedContext -> PPtr Word -> Kernel ()
> setConsumed scPtr buffer = do
>     consumed <- schedContextUpdateConsumed scPtr
>     tptr <- getCurThread
>     sent <- setMRs tptr (Just buffer) (setTimeArg consumed)
>     setMessageInfo tptr $ MI sent 0 0 0

> schedContextBindTCB :: PPtr SchedContext -> PPtr TCB -> Kernel ()
> schedContextBindTCB scPtr tcbPtr = do
>     sc <- getSchedContext scPtr
>     threadSet (\tcb -> tcb { tcbSchedContext = Just scPtr }) tcbPtr
>     setSchedContext scPtr $ sc { scTCB = Just tcbPtr }
>     schedContextResume scPtr
>     schedulable <- isSchedulable tcbPtr
>     when schedulable $ do
>         tcbSchedEnqueue tcbPtr
>         rescheduleRequired

> schedContextBindNtfn :: PPtr SchedContext -> PPtr Notification -> Kernel ()
> schedContextBindNtfn sc ntfn = do
>     n <- getNotification ntfn
>     setNotification ntfn (n { ntfnSc = Just sc })
>     s <- getSchedContext sc
>     setSchedContext sc (s { scNtfn = Just ntfn })

> schedContextUnbindTCB :: PPtr SchedContext -> Kernel ()
> schedContextUnbindTCB scPtr = do
>     sc <- getSchedContext scPtr
>     let tptrOpt = scTCB sc
>     assert (tptrOpt /= Nothing) "schedContextUnbind: option of TCB pointer must not be Nothing"
>     let tptr = fromJust tptrOpt
>     cur <- getCurThread
>     when (tptr == cur) $ rescheduleRequired
>     tcbSchedDequeue tptr
>     tcbReleaseRemove tptr
>     threadSet (\tcb -> tcb { tcbSchedContext = Nothing }) tptr
>     setSchedContext scPtr $ sc { scTCB = Nothing }

> schedContextUnbindNtfn :: PPtr SchedContext -> Kernel ()
> schedContextUnbindNtfn scPtr = do
>     sc <- getSchedContext scPtr
>     case scNtfn sc of
>         Nothing -> return ()
>         Just ntfnPtr -> (\ntfn -> do
>             setSchedContext scPtr (sc { scNtfn = Nothing })
>             n <- getNotification ntfn
>             setNotification ntfn (n { ntfnSc = Nothing })) ntfnPtr

> schedContextMaybeUnbindNtfn :: PPtr Notification -> Kernel ()
> schedContextMaybeUnbindNtfn ntfnPtr = do
>     scOpt <- liftM ntfnSc $ getNotification ntfnPtr
>     case scOpt of
>         Nothing -> return ()
>         Just sc -> schedContextUnbindNtfn sc

> schedContextUnbindAllTCBs :: PPtr SchedContext -> Kernel ()
> schedContextUnbindAllTCBs scPtr = do
>     sc <- getSchedContext scPtr
>     when (scTCB sc /= Nothing) $ schedContextUnbindTCB scPtr

> schedContextCancelYieldTo :: PPtr TCB -> Kernel ()
> schedContextCancelYieldTo tptr = do
>     scPtrOpt <- threadGet tcbYieldTo tptr
>     when (scPtrOpt /= Nothing) $ do
>         scPtr <- return $ fromJust scPtrOpt
>         sc <- getSchedContext scPtr
>         setSchedContext scPtr (sc { scYieldFrom = Nothing })
>         threadSet (\tcb -> tcb { tcbYieldTo = Nothing }) tptr

> schedContextCompleteYieldTo :: PPtr TCB -> Kernel ()
> schedContextCompleteYieldTo tptr = do
>     scPtrOpt <- threadGet tcbYieldTo tptr
>     when (scPtrOpt /= Nothing) $ do
>         scPtr <- return $ fromJust scPtrOpt
>         bufferOpt <- lookupIPCBuffer True tptr
>         case bufferOpt of
>             Nothing -> fail "schedContextCompleteYieldTo: buffer must not be Nothing"
>             Just buffer -> do
>                 setConsumed scPtr buffer
>                 schedContextCancelYieldTo tptr

> postpone :: PPtr SchedContext -> Kernel ()
> postpone scPtr = do
>     sc <- getSchedContext scPtr
>     tptr <- return $ fromJust $ scTCB sc
>     tcbSchedDequeue tptr
>     tcbReleaseEnqueue tptr
>     setReprogramTimer True

> schedContextResume :: PPtr SchedContext -> Kernel ()
> schedContextResume scPtr = do
>     sc <- getSchedContext scPtr
>     tptrOpt <- return $ scTCB sc
>     assert (tptrOpt /= Nothing) "schedContextResume: option of TCB pointer must not be Nothing"
>     tptr <- return $ fromJust tptrOpt
>     schedulable <- isSchedulable tptr
>     when schedulable $ do
>         ready <- refillReady scPtr
>         sufficient <- refillSufficient scPtr 0
>         when (not ready && sufficient) $ postpone scPtr

> contextYieldToUpdateQueues :: PPtr SchedContext -> Kernel Bool
> contextYieldToUpdateQueues scPtr = do
>     sc <- getSchedContext scPtr
>     tptr <- return $ fromJust $ scTCB sc
>     schedulable <- isSchedulable tptr
>     if schedulable
>         then do
>             refillUnblockCheck scPtr
>             ctPtr <- getCurThread
>             curprio <- threadGet tcbPriority ctPtr
>             prio <- threadGet tcbPriority tptr
>             if prio < curprio
>                 then do
>                     tcbSchedDequeue tptr
>                     tcbSchedEnqueue tptr
>                     return True
>                 else do
>                     threadSet (\tcb -> tcb { tcbYieldTo = Just scPtr }) ctPtr
>                     setSchedContext scPtr (sc { scYieldFrom = Just ctPtr })
>                     tcbSchedDequeue tptr
>                     tcbSchedEnqueue ctPtr
>                     tcbSchedEnqueue tptr
>                     rescheduleRequired
>                     return False
>         else return True

> schedContextYieldTo :: PPtr SchedContext -> [Word] -> Kernel ()
> schedContextYieldTo scPtr buffer = do
>     sc <- getSchedContext scPtr
>     scYieldFromOpt <- return $ scYieldFrom sc
>     when (scYieldFromOpt /= Nothing) $
>         schedContextCompleteYieldTo $ fromJust scYieldFromOpt
>     schedContextResume scPtr
>     return_now <- contextYieldToUpdateQueues scPtr
>     when return_now $ setConsumed scPtr (PPtr (head buffer))

> invokeSchedContext :: SchedContextInvocation -> KernelP ()
> invokeSchedContext iv = withoutPreemption $ case iv of
>     InvokeSchedContextConsumed scPtr buffer -> setConsumed scPtr (PPtr (head buffer))
>     InvokeSchedContextBind scPtr cap -> case cap of
>         ThreadCap tcbPtr -> schedContextBindTCB scPtr tcbPtr
>         NotificationCap ntfnPtr _ _ _ -> schedContextBindNtfn scPtr ntfnPtr
>         _ -> return ()
>     InvokeSchedContextUnbindObject scPtr cap -> case cap of
>         ThreadCap _ -> schedContextUnbindTCB scPtr
>         NotificationCap _ _ _ _ -> schedContextUnbindNtfn scPtr
>         _ -> return ()
>     InvokeSchedContextUnbind scPtr -> do
>         schedContextUnbindAllTCBs scPtr
>         schedContextUnbindNtfn scPtr
>         sc <- getSchedContext scPtr
>         let replyPtrOpt = scReply sc
>         when (replyPtrOpt /= Nothing) $ do
>             let replyPtr = fromJust replyPtrOpt
>             reply <- getReply replyPtr
>             setReply replyPtr (reply { replySc = Nothing })
>             setSchedContext scPtr $ sc { scReply = Nothing }
>     InvokeSchedContextYieldTo scPtr buffer -> do
>         schedContextYieldTo scPtr buffer

> getTCBSc :: PPtr TCB -> Kernel SchedContext
> getTCBSc tcbPtr = do
>     scOpt <- threadGet tcbSchedContext tcbPtr
>     assert (scOpt /= Nothing) "getTCBSc: SchedContext pointer must not be Nothing"
>     getSchedContext $ fromJust scOpt

> getScTime :: PPtr TCB -> Kernel Time
> getScTime tcbPtr = do
>     sc <- getTCBSc tcbPtr
>     return $ rTime (refillHd sc)

> schedContextDonate :: PPtr SchedContext -> PPtr TCB -> Kernel ()
> schedContextDonate scPtr tcbPtr = do
>     sc <- getSchedContext scPtr
>     fromOpt <- return $ scTCB sc
>     when (fromOpt /= Nothing) $ do
>         from <- return $ fromJust fromOpt
>         tcbSchedDequeue from
>         threadSet (\tcb -> tcb { tcbSchedContext = Nothing }) from
>         cur <- getCurThread
>         action <- getSchedulerAction
>         case action of
>             SwitchToThread candidate | candidate == from -> rescheduleRequired
>             _ -> when (from == cur) rescheduleRequired
>     setSchedContext scPtr (sc { scTCB = Just tcbPtr })
>     threadSet (\tcb -> tcb { tcbSchedContext = Just scPtr }) tcbPtr

> invokeSchedControlConfigure :: SchedControlInvocation -> KernelP ()
> invokeSchedControlConfigure iv = withoutPreemption $ case iv of
>     InvokeSchedControlConfigure scPtr budget period mRefills badge -> do
>         sc <- getSchedContext scPtr
>         setSchedContext scPtr $ sc { scBadge = badge }
>         when (scTCB sc /= Nothing) $ do
>             tcbReleaseRemove $ fromJust $ scTCB sc
>             tcbSchedDequeue $ fromJust $ scTCB sc
>             curSc <- getCurSc
>             when (curSc == scPtr) $ do
>                 budgetEnough <- checkBudget
>                 when budgetEnough $ commitTime

>         sc <- getSchedContext scPtr
>         runnable <- isRunnable $ fromJust $ scTCB sc
>         if scRefillMax sc > 0 && scTCB sc /= Nothing && runnable
>             then refillUpdate scPtr period budget mRefills
>             else refillNew scPtr mRefills budget period

>         sc <- getSchedContext scPtr
>         when (scTCB sc /= Nothing && scRefillMax sc > 0) $ do
>             schedContextResume scPtr
>             ctPtr <- getCurThread
>             if (fromJust $ scTCB sc) == ctPtr
>                 then rescheduleRequired
>                 else when runnable $ possibleSwitchTo $ fromJust $ scTCB sc

> refillAbsoluteMax :: Capability -> Int
> refillAbsoluteMax (SchedContextCap _ bits) = 1 `shiftL` bits - coreSchedContextBytes - refillSizeBytes
> refillAbsoluteMax _ = 0

> isRoundRobin :: PPtr SchedContext -> Kernel Bool
> isRoundRobin scPtr = do
>     sc <- getSchedContext scPtr
>     return (scPeriod sc == 0)

> isCurDomainExpired :: Kernel Bool
> isCurDomainExpired = do
>     domainTime <- getDomainTime
>     consumedTime <- getConsumedTime
>     return $! domainTime < consumedTime + minBudget

> commitTime :: Kernel ()
> commitTime = do
>     scPtr <- getCurSc
>     sc <- getSchedContext scPtr
>     consumed <- getConsumedTime
>     when (scRefillMax sc > 0) $ do
>         when (0 < consumed) $ do
>             rf <- refillSufficient scPtr consumed
>             assert rf "head refill must be sufficient to charge ksConsumed"
>             rr <- refillReady scPtr
>             assert rr "must be ready to use"
>             robin <- isRoundRobin scPtr
>             if robin
>                 then do
>                     rsz <- refillSize scPtr
>                     assert (rsz == minRefills) "we consume head; it should have minRefills budget"
>                     refills <- getRefills scPtr
>                     let newHd = (refillHd sc) { rAmount = rAmount (refillHd sc) - consumed }
>                     let newTl = (refillTl sc) { rAmount = rAmount (refillTl sc) + consumed }
>                     let refills' = replaceAt (scRefillHead sc) refills newHd
>                     let refills'' = replaceAt (scRefillTail sc) refills' newTl
>                     setRefills scPtr refills''
>                 else refillSplitCheck scPtr consumed
>         sc' <- getSchedContext scPtr
>         setSchedContext scPtr (sc' { scConsumed = scConsumed sc' + consumed })
>     when (numDomains > 1) $ do
>         domainTime <- getDomainTime
>         setDomainTime (domainTime - consumed)
>     setConsumedTime 0

> rollbackTime :: Kernel ()
> rollbackTime = do
>     reprogram <- getReprogramTimer
>     consumed <- getConsumedTime
>     assert (not reprogram || consumed == 0) "rollbackTime: it is invalid to rollback time if we have already acted on the new time"
>     curTime <- getCurTime
>     setCurTime (curTime - consumed)
>     setConsumedTime 0

> updateTimeStamp :: Kernel ()
> updateTimeStamp = do
>     prevTime <- getCurTime
>     curTime' <- doMachineOp getCurrentTime
>     setCurTime curTime'
>     setConsumedTime (curTime' - prevTime)

> maybeDonateSc :: PPtr TCB -> PPtr Notification -> Kernel ()
> maybeDonateSc tcbPtr ntfnPtr = do
>     scOpt <- threadGet tcbSchedContext tcbPtr
>     when (scOpt == Nothing) $ do
>         scPtrOpt <- liftM ntfnSc (getNotification ntfnPtr)
>         case scPtrOpt of
>             Nothing -> return ()
>             Just scPtr -> do
>                 scTCB <- liftM scTCB $ getSchedContext scPtr
>                 when (scTCB == Nothing) $ do
>                     schedContextDonate scPtr tcbPtr
>                     refillUnblockCheck scPtr
>                     schedContextResume scPtr

> maybeReturnSc :: PPtr Notification -> PPtr TCB -> Kernel ()
> maybeReturnSc ntfnPtr tcbPtr = do
>     nscOpt <- liftM ntfnSc $ getNotification ntfnPtr
>     tscOpt <- threadGet tcbSchedContext tcbPtr
>     when (nscOpt == tscOpt) $ do
>         threadSet (\tcb -> tcb { tcbSchedContext = Nothing }) tcbPtr
>         scPtr <- return $ fromJust nscOpt
>         sc <- getSchedContext scPtr
>         setSchedContext scPtr (sc { scTCB = Nothing })

> tcbReleaseEnqueue :: PPtr TCB -> Kernel ()
> tcbReleaseEnqueue tcbPtr = do
>     time <- getScTime tcbPtr
>     qs <- getReleaseQueue
>     times <- mapM getScTime qs
>     qst <- return $ zip qs times
>     qst' <- return $ filter (\(_,t') -> t' <= time) qst ++ [(tcbPtr, time)] ++ filter (\(_,t') -> not (t' <= time)) qst
>     setReleaseQueue (map fst qst')
>     threadSet (\t -> t { tcbInReleaseQueue = True }) tcbPtr

> tcbReleaseDequeue :: Kernel (PPtr TCB)
> tcbReleaseDequeue = do
>     qs <- getReleaseQueue
>     tcbPtr <- return $ head qs
>     setReleaseQueue $ tail qs
>     threadSet (\t -> t { tcbInReleaseQueue = False }) tcbPtr
>     setReprogramTimer True
>     return tcbPtr
