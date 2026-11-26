import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20438

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C : Circuit :=
  ⟨[⟨GateOp.and, [4, 9]⟩, ⟨GateOp.or, [10, 1]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.or, [4, 9]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [16, 17]⟩], 18⟩

theorem fanC : FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

theorem sizeC : C.size ≤ 9 := by decide

theorem repC : PEqualNP.Represents.Represents (fun u v : Fin 5 => (16269393 : ℕ).testBit (5 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_20438

theorem PEqualNP.Outside.L_meta_20438 :
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
    C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16269393 : ℕ).testBit (5 * u.val + v.val)) C) :=
  ⟨PEqualNP.Outside.L_meta_20438.C, PEqualNP.Outside.L_meta_20438.fanC,
    PEqualNP.Outside.L_meta_20438.sizeC, PEqualNP.Outside.L_meta_20438.repC⟩
