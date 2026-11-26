import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19571

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C : Circuit :=
  ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.or, [12, 0]⟩, ⟨GateOp.or, [13, 5]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.not, [15]⟩, ⟨GateOp.and, [14, 16]⟩], 17⟩

theorem fanC : FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

theorem sizeC : C.size ≤ 9 := by decide

theorem repC : PEqualNP.Represents.Represents (fun u v : Fin 5 => (7570494 : ℕ).testBit (5 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_19571

theorem PEqualNP.Outside.L_meta_19571 :
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
    C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7570494 : ℕ).testBit (5 * u.val + v.val)) C) :=
  ⟨PEqualNP.Outside.L_meta_19571.C, PEqualNP.Outside.L_meta_19571.fanC,
    PEqualNP.Outside.L_meta_19571.sizeC, PEqualNP.Outside.L_meta_19571.repC⟩
