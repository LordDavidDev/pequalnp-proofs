import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19714

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C : Circuit :=
  ⟨[⟨GateOp.or, [6, 15]⟩, ⟨GateOp.or, [9, 0]⟩, ⟨GateOp.or, [1, 17]⟩, ⟨GateOp.or, [13, 5]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [8, 20]⟩, ⟨GateOp.or, [7, 11]⟩, ⟨GateOp.or, [16, 23]⟩, ⟨GateOp.or, [5, 17]⟩, ⟨GateOp.or, [14, 3]⟩, ⟨GateOp.or, [2, 26]⟩, ⟨GateOp.or, [2, 25]⟩, ⟨GateOp.or, [16, 19]⟩, ⟨GateOp.or, [26, 26]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.or, [27, 12]⟩, ⟨GateOp.or, [19, 22]⟩, ⟨GateOp.or, [10, 23]⟩, ⟨GateOp.or, [3, 28]⟩, ⟨GateOp.or, [27, 35]⟩, ⟨GateOp.and, [34, 31]⟩, ⟨GateOp.or, [21, 24]⟩, ⟨GateOp.and, [29, 37]⟩, ⟨GateOp.or, [40, 5]⟩, ⟨GateOp.and, [24, 28]⟩, ⟨GateOp.or, [24, 18]⟩, ⟨GateOp.or, [40, 32]⟩, ⟨GateOp.and, [28, 39]⟩, ⟨GateOp.and, [33, 43]⟩, ⟨GateOp.and, [21, 34]⟩, ⟨GateOp.or, [46, 45]⟩, ⟨GateOp.or, [44, 48]⟩, ⟨GateOp.or, [49, 38]⟩], 50⟩

theorem fanC : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp

theorem sizeC : C.size ≤ 35 := by decide

theorem repC : PEqualNP.Represents.Represents (fun u v : Fin 8 => (17464622044026729945 : ℕ).testBit (8 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_19714

theorem PEqualNP.Outside.L_meta_19714 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17464622044026729945 : ℕ).testBit (8 * u.val + v.val)) 35 :=
  ⟨PEqualNP.Outside.L_meta_19714.C, PEqualNP.Outside.L_meta_19714.fanC,
   PEqualNP.Outside.L_meta_19714.sizeC, PEqualNP.Outside.L_meta_19714.repC⟩
