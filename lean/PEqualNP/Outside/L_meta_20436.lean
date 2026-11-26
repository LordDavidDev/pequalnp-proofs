import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20436

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C : Circuit :=
  ⟨[⟨GateOp.or, [5, 8]⟩, ⟨GateOp.and, [10, 1]⟩, ⟨GateOp.or, [11, 9]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [14, 5]⟩, ⟨GateOp.and, [13, 15]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [16, 17]⟩], 18⟩

theorem fanC : FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst g <;> simp

theorem sizeC : C.size ≤ 9 := by decide

theorem repC : PEqualNP.Represents.Represents (fun u v : Fin 5 => (15762641 : ℕ).testBit (5 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_20436

theorem PEqualNP.Outside.L_meta_20436 :
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
    C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (15762641 : ℕ).testBit (5 * u.val + v.val)) C) :=
  ⟨PEqualNP.Outside.L_meta_20436.C, PEqualNP.Outside.L_meta_20436.fanC,
    PEqualNP.Outside.L_meta_20436.sizeC, PEqualNP.Outside.L_meta_20436.repC⟩
