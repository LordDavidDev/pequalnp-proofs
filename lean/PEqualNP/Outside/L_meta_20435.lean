import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20435

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C : Circuit :=
  ⟨[⟨GateOp.or, [1, 9]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [11, 12]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [13, 14]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [15, 16]⟩], 17⟩

theorem fanC : FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

theorem sizeC : C.size ≤ 9 := by decide

theorem repC : PEqualNP.Represents.Represents (fun u v : Fin 5 => (15762513 : ℕ).testBit (5 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_20435

theorem PEqualNP.Outside.L_meta_20435 :
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
    C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (15762513 : ℕ).testBit (5 * u.val + v.val)) C) :=
  ⟨PEqualNP.Outside.L_meta_20435.C, PEqualNP.Outside.L_meta_20435.fanC,
    PEqualNP.Outside.L_meta_20435.sizeC, PEqualNP.Outside.L_meta_20435.repC⟩
