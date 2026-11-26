import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19600

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.or, [12, 0]⟩, ⟨GateOp.or, [13, 8]⟩, ⟨GateOp.not, [14]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [16, 0]⟩, ⟨GateOp.or, [15, 17]⟩], 18⟩

theorem fanC : FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

theorem sizeC : C.size ≤ 9 := by decide

theorem repC : PEqualNP.Represents.Represents (fun u v : Fin 5 => (24874092 : ℕ).testBit (5 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_19600

theorem PEqualNP.Outside.L_meta_19600 :
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
    C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24874092 : ℕ).testBit (5 * u.val + v.val)) C) :=
  ⟨PEqualNP.Outside.L_meta_19600.C, PEqualNP.Outside.L_meta_19600.fanC,
    PEqualNP.Outside.L_meta_19600.sizeC, PEqualNP.Outside.L_meta_19600.repC⟩
