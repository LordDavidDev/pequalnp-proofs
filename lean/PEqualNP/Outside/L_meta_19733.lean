import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19733

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C : Circuit :=
  ⟨[⟨GateOp.or, [12, 1]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [8, 7]⟩, ⟨GateOp.or, [13, 4]⟩, ⟨GateOp.and, [15, 3]⟩, ⟨GateOp.or, [5, 10]⟩, ⟨GateOp.or, [11, 2]⟩, ⟨GateOp.or, [20, 9]⟩, ⟨GateOp.or, [0, 23]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.or, [3, 21]⟩, ⟨GateOp.or, [17, 22]⟩, ⟨GateOp.and, [24, 2]⟩, ⟨GateOp.or, [16, 15]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [16, 21]⟩, ⟨GateOp.or, [31, 24]⟩, ⟨GateOp.or, [30, 18]⟩, ⟨GateOp.or, [21, 14]⟩, ⟨GateOp.or, [26, 32]⟩, ⟨GateOp.and, [35, 22]⟩, ⟨GateOp.or, [35, 17]⟩, ⟨GateOp.or, [20, 7]⟩, ⟨GateOp.or, [33, 14]⟩, ⟨GateOp.or, [19, 36]⟩, ⟨GateOp.or, [29, 37]⟩, ⟨GateOp.and, [41, 40]⟩, ⟨GateOp.or, [39, 29]⟩, ⟨GateOp.and, [34, 25]⟩, ⟨GateOp.or, [27, 32]⟩, ⟨GateOp.or, [16, 21]⟩, ⟨GateOp.and, [43, 45]⟩, ⟨GateOp.or, [42, 47]⟩, ⟨GateOp.or, [44, 48]⟩], 49⟩

theorem fanC : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp

theorem sizeC : C.size ≤ 34 := by decide

theorem repC : PEqualNP.Represents.Represents (fun u v : Fin 8 => (17388182210000334840 : ℕ).testBit (8 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_19733

theorem PEqualNP.Outside.L_meta_19733 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17388182210000334840 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨PEqualNP.Outside.L_meta_19733.C, PEqualNP.Outside.L_meta_19733.fanC,
   PEqualNP.Outside.L_meta_19733.sizeC, PEqualNP.Outside.L_meta_19733.repC⟩
