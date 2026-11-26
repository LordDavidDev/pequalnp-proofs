import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19599

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C : Circuit :=
  ⟨[⟨GateOp.or, [0, 5]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [12, 8]⟩, ⟨GateOp.and, [11, 13]⟩, ⟨GateOp.or, [5, 9]⟩, ⟨GateOp.and, [15, 0]⟩, ⟨GateOp.or, [14, 16]⟩, ⟨GateOp.not, [17]⟩], 18⟩

theorem fanC : FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

theorem sizeC : C.size ≤ 9 := by decide

theorem repC : PEqualNP.Represents.Represents (fun u v : Fin 5 => (24871982 : ℕ).testBit (5 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_19599

theorem PEqualNP.Outside.L_meta_19599 :
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
    C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (24871982 : ℕ).testBit (5 * u.val + v.val)) C) :=
  ⟨PEqualNP.Outside.L_meta_19599.C, PEqualNP.Outside.L_meta_19599.fanC,
    PEqualNP.Outside.L_meta_19599.sizeC, PEqualNP.Outside.L_meta_19599.repC⟩
