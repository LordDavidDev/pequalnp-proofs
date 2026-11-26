import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19710

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C : Circuit :=
  ⟨[⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [2, 10]⟩, ⟨GateOp.or, [15, 4]⟩, ⟨GateOp.and, [12, 1]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.or, [14, 7]⟩, ⟨GateOp.or, [16, 0]⟩, ⟨GateOp.or, [17, 18]⟩, ⟨GateOp.or, [14, 17]⟩, ⟨GateOp.and, [22, 21]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.or, [19, 18]⟩, ⟨GateOp.or, [3, 13]⟩, ⟨GateOp.or, [20, 17]⟩, ⟨GateOp.or, [1, 22]⟩, ⟨GateOp.or, [21, 29]⟩, ⟨GateOp.and, [31, 28]⟩, ⟨GateOp.or, [8, 27]⟩, ⟨GateOp.and, [30, 33]⟩, ⟨GateOp.or, [24, 11]⟩, ⟨GateOp.and, [23, 20]⟩, ⟨GateOp.and, [35, 26]⟩, ⟨GateOp.or, [25, 36]⟩, ⟨GateOp.or, [14, 35]⟩, ⟨GateOp.or, [1, 37]⟩, ⟨GateOp.or, [34, 32]⟩, ⟨GateOp.or, [38, 41]⟩, ⟨GateOp.or, [37, 42]⟩], 43⟩

theorem fanC : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp

theorem sizeC : C.size ≤ 28 := by decide

theorem repC : PEqualNP.Represents.Represents (fun u v : Fin 8 => (4081470838034108865 : ℕ).testBit (8 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_19710

theorem PEqualNP.Outside.L_meta_19710 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4081470838034108865 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_meta_19710.C, PEqualNP.Outside.L_meta_19710.fanC,
   PEqualNP.Outside.L_meta_19710.sizeC, PEqualNP.Outside.L_meta_19710.repC⟩
