import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19605

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C : Circuit :=
  ⟨[⟨GateOp.or, [1, 8]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [12, 6]⟩, ⟨GateOp.and, [11, 13]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [16, 17]⟩], 18⟩

theorem fanC : FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

theorem sizeC : C.size ≤ 9 := by decide

theorem repC : PEqualNP.Represents.Represents (fun u v : Fin 5 => (3251479 : ℕ).testBit (5 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_19605

theorem PEqualNP.Outside.L_meta_19605 :
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
    C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3251479 : ℕ).testBit (5 * u.val + v.val)) C) :=
  ⟨PEqualNP.Outside.L_meta_19605.C, PEqualNP.Outside.L_meta_19605.fanC,
    PEqualNP.Outside.L_meta_19605.sizeC, PEqualNP.Outside.L_meta_19605.repC⟩
