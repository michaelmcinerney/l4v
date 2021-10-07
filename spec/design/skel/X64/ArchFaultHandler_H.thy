(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Fault Handlers"

theory ArchFaultHandler_H
imports TCB_H Structures_H
begin

context Arch begin global_naming X64_H

#INCLUDE_HASKELL_PREPARSE SEL4/API/Failures/X64.lhs

#INCLUDE_HASKELL SEL4/API/Faults/X64.lhs decls_only
#INCLUDE_HASKELL SEL4/API/Faults/X64.lhs bodies_only

end

end
