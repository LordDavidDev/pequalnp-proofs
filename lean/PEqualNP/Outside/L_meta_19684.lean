import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19684_aux

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
  ⟨[⟨.or, [7, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [9, 0]⟩, ⟨.or, [12, 10]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [14, 8]⟩, ⟨.and, [16, 13]⟩, ⟨.not, [17]⟩, ⟨.and, [18, 15]⟩], 19⟩

theorem main :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 10 ∧
      Represents (fun u v : Fin 5 => (11911734 : ℕ).testBit (5 * u.val + v.val)) C :=
  ⟨C_, fanInTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19684_aux

theorem PEqualNP.Outside.L_meta_19684 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (11911734 : ℕ).testBit (5 * u.val + v.val)) C) :=
  PEqualNP.Outside.L_meta_19684_aux.main
