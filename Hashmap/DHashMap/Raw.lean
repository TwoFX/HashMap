/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro, Markus Himmel
-/
import Hashmap.DHashMap.Internal.AssocList.Basic

/-!
# Definition of `DHashMap.Raw`

This file defines the type `Std.DHashMap.Raw`. All of its functions are defined in the module
`Std.DHashMap.Basic`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

namespace Std.DHashMap

structure Raw (α : Type u) (β : α → Type v) where
  size : Nat
  buckets : Array (DHashMap.Internal.AssocList α β)

end Std.DHashMap
