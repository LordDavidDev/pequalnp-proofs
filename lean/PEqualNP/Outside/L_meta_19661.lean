import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19661_aux

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
  ⟨[⟨.or, [2, 0]⟩, ⟨.or, [7, 6]⟩, ⟨.or, [5, 2]⟩, ⟨.and, [11, 0]⟩, ⟨.or, [9, 1]⟩, ⟨.or, [14, 10]⟩, ⟨.and, [14, 12]⟩, ⟨.not, [15]⟩, ⟨.or, [16, 13]⟩, ⟨.or, [18, 17]⟩], 19⟩

theorem main :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 10 ∧
      Represents (fun u v : Fin 5 => (16236582 : ℕ).testBit (5 * u.val + v.val)) C :=
  ⟨C_, fanInTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19661_aux

theorem PEqualNP.Outside.L_meta_19661 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16236582 : ℕ).testBit (5 * u.val + v.val)) C) :=
  PEqualNP.Outside.L_meta_19661_aux.main
