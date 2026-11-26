import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19660_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def fanInTwoB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with
      | GateOp.and => true
      | GateOp.or => true
      | GateOp.not => true
      | _ => false) &&
    Nat.ble g.inputs.length 2

theorem fanInTwoB_sound (C : Circuit) (h : fanInTwoB C = true) : FanInTwo C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

def C_ : Circuit :=
  ⟨[⟨.or, [7, 1]⟩, ⟨.or, [9, 2]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [10, 6]⟩, ⟨.not, [11]⟩, ⟨.or, [15, 14]⟩, ⟨.or, [16, 0]⟩, ⟨.or, [13, 12]⟩, ⟨.and, [18, 17]⟩], 19⟩

theorem main :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 10 ∧
      Represents (fun u v : Fin 5 => ((15768113 : ℕ).testBit (5 * u.val + v.val))) C :=
  ⟨C_, fanInTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19660_aux

theorem PEqualNP.Outside.L_meta_19660 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (15768113 : ℕ).testBit (5 * u.val + v.val)) C) :=
  PEqualNP.Outside.L_meta_19660_aux.main
