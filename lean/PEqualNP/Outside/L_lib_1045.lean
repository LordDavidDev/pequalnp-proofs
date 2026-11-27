import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1045

noncomputable def w {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (π : Equiv.Perm (Fin n)) : ℝ :=
  ∏ j : Fin n, M (π j) j

noncomputable def mu {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : ℝ :=
  ∑ π : Equiv.Perm (Fin n), if π j = i then w M π else 0

noncomputable def chi {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Fin n × Fin n → Bool) : ℝ :=
  ∏ i : Fin n, if s (σ i, i) then (-1 : ℝ) else 1

theorem w_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (π : Equiv.Perm (Fin n)) : 0 ≤ w A π :=
  Finset.prod_nonneg fun j _ => hA _ _

theorem mu_pos_entry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (i j : Fin n) (h : 0 < mu A i j) : 0 < A i j := by
  rcases (hA i j).lt_or_eq with h1 | h1
  · exact h1
  · exfalso
    have : mu A i j = 0 := by
      unfold mu
      refine Finset.sum_eq_zero fun π _ => ?_
      by_cases hp : π j = i
      · simp only [hp, ↓reduceIte]
        unfold w
        refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
        rw [hp]; exact h1.symm
      · simp only [hp, ↓reduceIte]
    linarith

theorem w_pos_mu_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (π : Equiv.Perm (Fin n)) (h : 0 < w A π) (j : Fin n) : 0 < mu A (π j) j := by
  unfold mu
  have h1 : (if π j = π j then w A π else 0) ≤
      ∑ τ : Equiv.Perm (Fin n), if τ j = π j then w A τ else 0 :=
    Finset.single_le_sum (f := fun τ : Equiv.Perm (Fin n) => if τ j = π j then w A τ else 0)
      (fun τ _ => by
        show 0 ≤ (if τ j = π j then w A τ else 0)
        split_ifs
        · exact w_nonneg A hA τ
        · exact le_refl _) (Finset.mem_univ π)
  simp only [↓reduceIte] at h1
  linarith

theorem w_pos_transfer {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j)
    (hmu : ∀ i j, mu A i j = mu B i j) (π : Equiv.Perm (Fin n)) (h : 0 < w A π) :
    (∀ j, 0 < A (π j) j) ∧ (∀ j, 0 < B (π j) j) := by
  constructor
  · intro j
    exact mu_pos_entry A hA _ _ (w_pos_mu_pos A hA π h j)
  · intro j
    refine mu_pos_entry B hB _ _ ?_
    rw [← hmu]
    exact w_pos_mu_pos A hA π h j

theorem log_sum {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (π : Equiv.Perm (Fin n))
    (h1 : ∀ j, 0 < A (π j) j) (h2 : ∀ j, 0 < B (π j) j) :
    (∑ j : Fin n, (Real.log (A (π j) j) - Real.log (B (π j) j))) =
      Real.log (w A π) - Real.log (w B π) := by
  unfold w
  rw [Real.log_prod, Real.log_prod, Finset.sum_sub_distrib]
  · intro j _; exact (h2 j).ne'
  · intro j _; exact (h1 j).ne'

theorem sum_T_zero {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hmu : ∀ i j, mu A i j = mu B i j) :
    (∑ π : Equiv.Perm (Fin n), (w A π - w B π) *
      ∑ j : Fin n, (Real.log (A (π j) j) - Real.log (B (π j) j))) = 0 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h1 : ∀ π : Equiv.Perm (Fin n),
      (w A π - w B π) * (Real.log (A (π j) j) - Real.log (B (π j) j)) =
      ∑ i : Fin n, if π j = i then
        (w A π - w B π) * (Real.log (A i j) - Real.log (B i j)) else 0 := by
    intro π
    simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h2 : (∑ π : Equiv.Perm (Fin n), if π j = i then
        (w A π - w B π) * (Real.log (A i j) - Real.log (B i j)) else 0) =
      (mu A i j - mu B i j) * (Real.log (A i j) - Real.log (B i j)) := by
    unfold mu
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun π _ => ?_
    split_ifs <;> ring
  rw [h2, hmu]; ring

theorem part1 {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j)
    (hmu : ∀ i j, mu A i j = mu B i j) (π : Equiv.Perm (Fin n)) : w A π = w B π := by
  have key : ∀ τ : Equiv.Perm (Fin n), (w A τ = 0 ∧ w B τ = 0) ∨
      (0 < w A τ ∧ 0 < w B τ ∧
        (∑ j : Fin n, (Real.log (A (τ j) j) - Real.log (B (τ j) j))) =
          Real.log (w A τ) - Real.log (w B τ)) := by
    intro τ
    rcases (w_nonneg A hA τ).lt_or_eq with h | h
    · right
      obtain ⟨h1, h2⟩ := w_pos_transfer A B hA hB hmu τ h
      exact ⟨h, Finset.prod_pos fun j _ => h2 j, log_sum A B τ h1 h2⟩
    · rcases (w_nonneg B hB τ).lt_or_eq with h' | h'
      · exfalso
        obtain ⟨h1, h2⟩ := w_pos_transfer B A hB hA (fun i j => (hmu i j).symm) τ h'
        have : 0 < w A τ := Finset.prod_pos fun j _ => h2 j
        linarith
      · left; exact ⟨h.symm, h'.symm⟩
  have hnn : ∀ τ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))), 0 ≤ (w A τ - w B τ) *
      ∑ j : Fin n, (Real.log (A (τ j) j) - Real.log (B (τ j) j)) := by
    intro τ _
    rcases key τ with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · rw [h1, h2]; simp
    · rw [h3]
      rcases le_total (w A τ) (w B τ) with h | h
      · have := Real.log_le_log h1 h
        nlinarith
      · have := Real.log_le_log h2 h
        nlinarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (sum_T_zero A B hmu) π (Finset.mem_univ π)
  rcases key π with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · rw [h1, h2]
  · rw [h3] at hz
    rcases mul_eq_zero.1 hz with h | h
    · linarith
    · exact Real.log_injOn_pos (Set.mem_Ioi.2 h1) (Set.mem_Ioi.2 h2) (by linarith)

theorem det_expand {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool) :
    Matrix.det (fun i j => if s (i,j) then -M i j else M i j : Matrix (Fin n) (Fin n) ℝ) =
      ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) * (chi σ s * w M σ) := by
  refine (Matrix.det_apply' _).trans ?_
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  unfold chi w
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : s (σ i, i) <;> simp [h]

theorem chi_flip_self {n : ℕ} (σ : Equiv.Perm (Fin n)) (i0 : Fin n) (s : Fin n × Fin n → Bool) :
    chi σ (Function.update s (σ i0, i0) (!s (σ i0, i0))) = - chi σ s := by
  unfold chi
  have h1 : ∀ i : Fin n, (if Function.update s (σ i0, i0) (!s (σ i0, i0)) (σ i, i) then (-1 : ℝ) else 1)
      = (if i = i0 then (-1 : ℝ) else 1) * (if s (σ i, i) then (-1 : ℝ) else 1) := by
    intro i
    by_cases h : i = i0
    · subst h
      rw [Function.update_self]
      cases s (σ i, i) <;> simp
    · have hne : (σ i, i) ≠ (σ i0, i0) := by
        intro h'
        exact h (Prod.ext_iff.1 h').2
      rw [Function.update_of_ne hne]
      simp [h]
  simp_rw [h1]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

theorem chi_flip_other {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (i0 : Fin n) (h : σ i0 ≠ τ i0)
    (s : Fin n × Fin n → Bool) :
    chi τ (Function.update s (σ i0, i0) (!s (σ i0, i0))) = chi τ s := by
  unfold chi
  refine Finset.prod_congr rfl fun i _ => ?_
  have hne : (τ i, i) ≠ (σ i0, i0) := by
    intro h'
    have h1 := (Prod.ext_iff.1 h').1
    have h2 := (Prod.ext_iff.1 h').2
    simp only at h1 h2
    subst h2
    exact h h1.symm
  rw [Function.update_of_ne hne]

theorem orth {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (h : σ ≠ τ) :
    (∑ s : Fin n × Fin n → Bool, chi σ s * chi τ s) = 0 := by
  have hex : ∃ i0, σ i0 ≠ τ i0 := by
    by_contra hc
    apply h
    ext i
    by_contra hi
    exact hc ⟨i, fun hh => hi (by rw [hh])⟩
  obtain ⟨i0, hi0⟩ := hex
  have hinv : Function.Involutive
      (fun s : Fin n × Fin n → Bool => Function.update s (σ i0, i0) (!s (σ i0, i0))) := by
    intro s
    funext x
    by_cases hx : x = (σ i0, i0)
    · subst hx; simp
    · simp [Function.update_of_ne hx]
  have hs := Fintype.sum_bijective _ hinv.bijective
    (fun s : Fin n × Fin n → Bool => -(chi σ s * chi τ s))
    (fun s : Fin n × Fin n → Bool => chi σ s * chi τ s)
    (fun s => by
      show -(chi σ s * chi τ s) = chi σ (Function.update s (σ i0, i0) (!s (σ i0, i0))) *
        chi τ (Function.update s (σ i0, i0) (!s (σ i0, i0)))
      rw [chi_flip_self, chi_flip_other σ τ i0 hi0]; ring)
  rw [Finset.sum_neg_distrib] at hs
  linarith

theorem chi_sq {n : ℕ} (τ : Equiv.Perm (Fin n)) (s : Fin n × Fin n → Bool) :
    chi τ s * chi τ s = 1 := by
  unfold chi
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs <;> norm_num

theorem part2 {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hdet : ∀ s : Fin n × Fin n → Bool,
      Matrix.det (fun i j => if s (i,j) then -A i j else A i j : Matrix (Fin n) (Fin n) ℝ) =
      Matrix.det (fun i j => if s (i,j) then -B i j else B i j : Matrix (Fin n) (Fin n) ℝ))
    (τ : Equiv.Perm (Fin n)) : w A τ = w B τ := by
  have h0 : ∀ s : Fin n × Fin n → Bool,
      (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) * (chi σ s * (w A σ - w B σ))) = 0 := by
    intro s
    have := hdet s
    rw [det_expand, det_expand] at this
    have h2 : (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) * (chi σ s * (w A σ - w B σ)))
        = (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) * (chi σ s * w A σ)) -
          ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) * (chi σ s * w B σ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun σ _ => ?_
      ring
    rw [h2, this]; ring
  have h1 : (∑ s : Fin n × Fin n → Bool, chi τ s *
      ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) * (chi σ s * (w A σ - w B σ))) = 0 := by
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [h0 s]; ring
  simp_rw [Finset.mul_sum] at h1
  rw [Finset.sum_comm] at h1
  have h3 : ∀ σ : Equiv.Perm (Fin n),
      (∑ s : Fin n × Fin n → Bool,
        chi τ s * (((Equiv.Perm.sign σ : ℤ) : ℝ) * (chi σ s * (w A σ - w B σ)))) =
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * (w A σ - w B σ) *
        ∑ s : Fin n × Fin n → Bool, chi σ s * chi τ s := by
    intro σ
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  simp_rw [h3] at h1
  rw [Finset.sum_eq_single τ (fun σ _ hσ => by rw [orth σ τ hσ]; ring)
    (fun hh => absurd (Finset.mem_univ τ) hh)] at h1
  simp_rw [chi_sq] at h1
  have hsg : ((Equiv.Perm.sign τ : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast Units.ne_zero (Equiv.Perm.sign τ)
  have hcard : (∑ s : Fin n × Fin n → Bool, (1 : ℝ)) ≠ 0 := by
    simp
  have h4 := mul_eq_zero.1 h1
  rcases h4 with h4 | h4
  · rcases mul_eq_zero.1 h4 with h5 | h5
    · exact absurd h5 hsg
    · linarith
  · exact absurd h4 hcard

theorem main (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) :
    ((∀ i j : Fin n, mu A i j = mu B i j) ↔ (∀ π : Equiv.Perm (Fin n), w A π = w B π)) ∧
    ((∀ s : Fin n × Fin n → Bool,
      Matrix.det (fun i j => if s (i,j) then -A i j else A i j : Matrix (Fin n) (Fin n) ℝ) =
      Matrix.det (fun i j => if s (i,j) then -B i j else B i j : Matrix (Fin n) (Fin n) ℝ)) ↔
      (∀ π : Equiv.Perm (Fin n), w A π = w B π)) := by
  refine ⟨⟨fun h π => part1 A B hA hB h π, fun h i j => ?_⟩,
    ⟨fun h π => part2 A B h π, fun h s => ?_⟩⟩
  · unfold mu
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [h π]
  · rw [det_expand, det_expand]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [h π]

end PEqualNP.Outside.L_lib_1045

theorem PEqualNP.Outside.L_lib_1045 : (∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ),
  (∀ i j, 0 ≤ A i j) → (∀ i j, 0 ≤ B i j) →
  let I := Fin n
  let w := fun (M : Matrix I I ℝ) (π : Equiv.Perm I) => ∏ j : I, M (π j) j
  let mu := fun (M : Matrix I I ℝ) (i j : I) =>
    ∑ π : Equiv.Perm I, if π j = i then w M π else 0
  let det := fun (M : Matrix I I ℝ) (s : I × I → Bool) =>
    Matrix.det (fun i j => if s (i,j) then -M i j else M i j : Matrix I I ℝ)
  ((∀ i j : I, mu A i j = mu B i j) ↔ (∀ π : Equiv.Perm I, w A π = w B π)) ∧
  ((∀ s : I × I → Bool, det A s = det B s) ↔ (∀ π : Equiv.Perm I, w A π = w B π))) := by
  intro n A B hA hB
  intro I w mu det
  exact PEqualNP.Outside.L_lib_1045.main n A B hA hB
