import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19725

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C : Circuit :=
  ⟨[⟨GateOp.or, [1, 10]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.or, [7, 6]⟩, ⟨GateOp.or, [5, 13]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.or, [4, 12]⟩, ⟨GateOp.and, [7, 16]⟩, ⟨GateOp.or, [14, 11]⟩, ⟨GateOp.or, [14, 21]⟩, ⟨GateOp.or, [17, 22]⟩, ⟨GateOp.or, [19, 10]⟩, ⟨GateOp.or, [17, 7]⟩, ⟨GateOp.or, [18, 2]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.or, [25, 9]⟩, ⟨GateOp.or, [19, 21]⟩, ⟨GateOp.or, [9, 26]⟩, ⟨GateOp.or, [28, 12]⟩, ⟨GateOp.or, [15, 30]⟩, ⟨GateOp.or, [11, 31]⟩, ⟨GateOp.or, [24, 2]⟩, ⟨GateOp.and, [23, 33]⟩, ⟨GateOp.or, [27, 29]⟩, ⟨GateOp.and, [35, 38]⟩, ⟨GateOp.or, [32, 3]⟩, ⟨GateOp.or, [37, 39]⟩, ⟨GateOp.and, [40, 36]⟩, ⟨GateOp.and, [30, 29]⟩, ⟨GateOp.and, [34, 20]⟩, ⟨GateOp.or, [42, 44]⟩, ⟨GateOp.and, [39, 20]⟩, ⟨GateOp.or, [27, 31]⟩, ⟨GateOp.or, [45, 41]⟩, ⟨GateOp.or, [43, 48]⟩], 49⟩

theorem fanC : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp

theorem sizeC : C.size ≤ 34 := by decide

theorem repC : PEqualNP.Represents.Represents (fun u v : Fin 8 => (8992515997758798780 : ℕ).testBit (8 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_19725

theorem PEqualNP.Outside.L_meta_19725 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8992515997758798780 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨PEqualNP.Outside.L_meta_19725.C, PEqualNP.Outside.L_meta_19725.fanC,
   PEqualNP.Outside.L_meta_19725.sizeC, PEqualNP.Outside.L_meta_19725.repC⟩
