import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19663

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C : Circuit :=
  ⟨[⟨GateOp.and, [4, 9]⟩, ⟨GateOp.or, [10, 1]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.or, [12, 6]⟩, ⟨GateOp.or, [13, 7]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [15, 9]⟩, ⟨GateOp.and, [14, 16]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [17, 18]⟩], 19⟩

theorem fanC : FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp

theorem sizeC : C.size ≤ 10 := by decide

theorem repC : PEqualNP.Represents.Represents (fun u v : Fin 5 => (16269521 : ℕ).testBit (5 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_19663

theorem PEqualNP.Outside.L_meta_19663 :
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
    C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16269521 : ℕ).testBit (5 * u.val + v.val)) C) :=
  ⟨PEqualNP.Outside.L_meta_19663.C, PEqualNP.Outside.L_meta_19663.fanC,
    PEqualNP.Outside.L_meta_19663.sizeC, PEqualNP.Outside.L_meta_19663.repC⟩
