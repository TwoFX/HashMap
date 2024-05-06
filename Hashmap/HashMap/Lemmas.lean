/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Hashmap.DHashMap.Lemmas
import Hashmap.HashMap.Basic

set_option autoImplicit false

universe u v

variable {α : Type u} {β : Type v} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]

namespace MyLean.HashMap

namespace Raw

variable (m : Raw α β) (h : m.WF)

-- theorem ext (m m' : Raw α β) : m.raw = m'.raw → m = m' := by
--   cases m; cases m'; rintro rfl; rfl

theorem findEntry?_insert {a k : α} {b : β} :
    (m.insert a b).findEntry? k = bif a == k then some (a, b) else m.findEntry? k := by
  simp [findEntry?, insert, DHashMap.Raw.findEntry?_insert _ h, apply_bif (Option.map Sigma.toProd)]

end Raw

section

variable (m : HashMap α β)

theorem findEntry?_insert {a k : α} {b : β} :
    (m.insert a b).findEntry? k = bif a == k then some (a, b) else m.findEntry? k := by
  simp [findEntry?, insert, DHashMap.findEntry?_insert, apply_bif (Option.map Sigma.toProd)]

end

end MyLean.HashMap
