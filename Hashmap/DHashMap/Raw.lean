/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro, Markus Himmel
-/
import Hashmap.DHashMap.Internal.AssocList.Basic

set_option autoImplicit false

universe u v

namespace MyLean.DHashMap

structure Raw (α : Type u) (β : α → Type v) where
  size : Nat
  buckets : Array (AssocList α β)

end MyLean.DHashMap
