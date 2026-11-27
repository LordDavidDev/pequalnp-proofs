import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1000

def hd {m q : ℕ} (x y : (Fin m → Fin q)) : ℕ := (Finset.univ.filter (fun i => x i ≠ y i)).card

theorem hd_comm {m q : ℕ} (x y : (Fin m → Fin q)) : hd x y = hd y x := by
  unfold hd
  congr 1
  ext i
  simp [ne_comm]

theorem hd_self {m q : ℕ} (x : (Fin m → Fin q)) : hd x x = 0 := by
  simp [hd]

theorem hd_eq_zero {m q : ℕ} {x y : (Fin m → Fin q)} (h : hd x y = 0) : x = y := by
  funext i
  by_contra hi
  have h1 : i ∈ Finset.univ.filter (fun i => x i ≠ y i) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩
  rw [hd, Finset.card_eq_zero] at h
  rw [h] at h1
  simp at h1

theorem hd_tri {m q : ℕ} (x y z : (Fin m → Fin q)) : hd x z ≤ hd x y + hd y z := by
  unfold hd
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
  by_cases h1 : x i = y i
  · right
    intro h2
    exact hi (h1.trans h2)
  · left
    exact h1

theorem hd_one {m q : ℕ} {c u : (Fin m → Fin q)} (h : hd c u = 1) :
    ∃ l, u l ≠ c l ∧ ∀ i, i ≠ l → u i = c i := by
  obtain ⟨l, hl⟩ := Finset.card_eq_one.1 h
  refine ⟨l, ?_, ?_⟩
  · have h1 : l ∈ Finset.univ.filter (fun i => c i ≠ u i) := by
      rw [hl]
      exact Finset.mem_singleton_self l
    exact Ne.symm (Finset.mem_filter.1 h1).2
  · intro i hi
    by_contra hne
    have h1 : i ∈ Finset.univ.filter (fun i => c i ≠ u i) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, Ne.symm hne⟩
    rw [hl] at h1
    exact hi (Finset.mem_singleton.1 h1)

theorem hd_ge_two {m q : ℕ} (x u : (Fin m → Fin q)) (a b : Fin m) (hab : a ≠ b)
    (ha : x a ≠ u a) (hb : x b ≠ u b) : 2 ≤ hd x u := by
  have hsub : ({a, b} : Finset (Fin m)) ⊆ Finset.univ.filter (fun i => x i ≠ u i) := by
    intro i hi
    rw [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h | h
    · rw [h]
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩
    · rw [h]
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_pair hab] at h1
  exact h1

theorem hd_ge_three {m q : ℕ} (x u : (Fin m → Fin q)) (a b c : Fin m) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c)
    (ha : x a ≠ u a) (hb : x b ≠ u b) (hc : x c ≠ u c) : 3 ≤ hd x u := by
  have hsub : ({a, b, c} : Finset (Fin m)) ⊆ Finset.univ.filter (fun i => x i ≠ u i) := by
    intro i hi
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h | h | h
    · rw [h]
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩
    · rw [h]
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩
    · rw [h]
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩
  have h1 := Finset.card_le_card hsub
  have h2 : ({a, b, c} : Finset (Fin m)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
  rw [h2] at h1
  exact h1

theorem upd_eq {m q : ℕ} (c u : (Fin m → Fin q)) (l : Fin m) (h : ∀ i, i ≠ l → u i = c i) :
    Function.update c l (u l) = u := by
  funext i
  by_cases hi : i = l
  · rw [hi]
    simp
  · rw [Function.update_of_ne hi, h i hi]

theorem adj_common {m q : ℕ} {c x : (Fin m → Fin q)} (N : Finset (Fin m → Fin q))
    (hN : ∀ u ∈ N, hd c u = 1) (hx : hd c x = 1) :
    (N.filter (fun u => hd x u = 1)).card ≤ q := by
  classical
  obtain ⟨l, hl1, hl2⟩ := hd_one hx
  have hsub : N.filter (fun u => hd x u = 1)
      ⊆ (Finset.univ : Finset (Fin q)).image (fun a => Function.update c l a) := by
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨l', h1, h2⟩ := hd_one (hN u hu.1)
    have hll : l' = l := by
      by_contra hne
      have h3 : 2 ≤ hd x u := hd_ge_two x u l l' (Ne.symm hne)
        (by rw [h2 l (Ne.symm hne)]; exact hl1)
        (by rw [hl2 l' hne]; exact Ne.symm h1)
      omega
    rw [hll] at h2
    exact Finset.mem_image.2 ⟨u l, Finset.mem_univ _, upd_eq c u l h2⟩
  calc (N.filter (fun u => hd x u = 1)).card
      ≤ ((Finset.univ : Finset (Fin q)).image (fun a => Function.update c l a)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin q)).card := Finset.card_image_le
    _ = q := by simp

theorem two_away {m q : ℕ} {c x : (Fin m → Fin q)} (N : Finset (Fin m → Fin q))
    (hN : ∀ u ∈ N, hd c u = 1) (hx : hd c x = 2) :
    (N.filter (fun u => hd x u ≤ 2)).card ≤ 2 * q ∧
    (N.filter (fun u => hd x u = 1)).card ≤ 2 := by
  classical
  obtain ⟨i, j, hij, hΔ⟩ := Finset.card_eq_two.1 hx
  have hmem : ∀ a, c a ≠ x a ↔ a = i ∨ a = j := by
    intro a
    have h1 : a ∈ Finset.univ.filter (fun i => c i ≠ x i) ↔ a ∈ ({i, j} : Finset (Fin m)) := by
      rw [hΔ]
    rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at h1
    constructor
    · intro h
      exact h1.1 ⟨Finset.mem_univ _, h⟩
    · intro h
      exact (h1.2 h).2
  have hxi : x i ≠ c i := Ne.symm ((hmem i).2 (Or.inl rfl))
  have hxj : x j ≠ c j := Ne.symm ((hmem j).2 (Or.inr rfl))
  have hxo : ∀ a, a ≠ i → a ≠ j → x a = c a := by
    intro a hai haj
    by_contra hne
    rcases (hmem a).1 (Ne.symm hne) with h | h
    · exact hai h
    · exact haj h
  have key : ∀ u ∈ N, hd x u ≤ 2 →
      ∃ l, (l = i ∨ l = j) ∧ u l ≠ c l ∧ ∀ a, a ≠ l → u a = c a := by
    intro u hu h2
    obtain ⟨l, h1, h2'⟩ := hd_one (hN u hu)
    refine ⟨l, ?_, h1, h2'⟩
    by_contra hcon
    have hli : l ≠ i := fun h => hcon (Or.inl h)
    have hlj : l ≠ j := fun h => hcon (Or.inr h)
    have h3 : 3 ≤ hd x u := hd_ge_three x u i j l hij (Ne.symm hli) (Ne.symm hlj)
      (by rw [h2' i (Ne.symm hli)]; exact hxi)
      (by rw [h2' j (Ne.symm hlj)]; exact hxj)
      (by rw [hxo l hli hlj]; exact Ne.symm h1)
    omega
  constructor
  · have hsub : N.filter (fun u => hd x u ≤ 2)
        ⊆ (Finset.univ : Finset (Fin q)).image (fun a => Function.update c i a)
          ∪ (Finset.univ : Finset (Fin q)).image (fun a => Function.update c j a) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨l, hl, _, h2⟩ := key u hu.1 hu.2
      rw [Finset.mem_union]
      rcases hl with h | h
      · left
        rw [h] at h2
        exact Finset.mem_image.2 ⟨u i, Finset.mem_univ _, upd_eq c u i h2⟩
      · right
        rw [h] at h2
        exact Finset.mem_image.2 ⟨u j, Finset.mem_univ _, upd_eq c u j h2⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le
      ((Finset.univ : Finset (Fin q)).image (fun a => Function.update c i a))
      ((Finset.univ : Finset (Fin q)).image (fun a => Function.update c j a))
    have h3 : ((Finset.univ : Finset (Fin q)).image (fun a => Function.update c i a)).card ≤ q := by
      have h4 := Finset.card_image_le (s := (Finset.univ : Finset (Fin q)))
        (f := fun a => Function.update c i a)
      simpa using h4
    have h5 : ((Finset.univ : Finset (Fin q)).image (fun a => Function.update c j a)).card ≤ q := by
      have h4 := Finset.card_image_le (s := (Finset.univ : Finset (Fin q)))
        (f := fun a => Function.update c j a)
      simpa using h4
    omega
  · have hsub : N.filter (fun u => hd x u = 1)
        ⊆ {Function.update c i (x i), Function.update c j (x j)} := by
      intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨l, hl, _, h2⟩ := key u hu.1 (by omega)
      rw [Finset.mem_insert, Finset.mem_singleton]
      rcases hl with h | h
      · left
        rw [h] at h2
        have h3 : u i = x i := by
          by_contra hne
          have h4 : 2 ≤ hd x u := hd_ge_two x u i j hij (Ne.symm hne)
            (by rw [h2 j (Ne.symm hij)]; exact hxj)
          omega
        rw [← h3]
        exact (upd_eq c u i h2).symm
      · right
        rw [h] at h2
        have h3 : u j = x j := by
          by_contra hne
          have h4 : 2 ≤ hd x u := hd_ge_two x u i j hij
            (by rw [h2 i hij]; exact hxi) (Ne.symm hne)
          omega
        rw [← h3]
        exact (upd_eq c u j h2).symm
    exact le_trans (Finset.card_le_card hsub) Finset.card_le_two

theorem split {m q : ℕ} (g : (Fin m → Fin q) → (Fin m → Fin q) → ℕ)
    (hg : ∀ x u, g x u = g u x) (A B : Finset (Fin m → Fin q)) (h : Disjoint A B) :
    ∑ x ∈ A ∪ B, ∑ u ∈ A ∪ B, g x u
      = ∑ x ∈ A, ∑ u ∈ A, g x u + 2 * ∑ x ∈ A, ∑ u ∈ B, g x u + ∑ x ∈ B, ∑ u ∈ B, g x u := by
  classical
  rw [Finset.sum_union h]
  simp only [Finset.sum_union h]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h1 : ∑ x ∈ B, ∑ u ∈ A, g x u = ∑ x ∈ A, ∑ u ∈ B, g x u := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro u _
    exact hg u x
  rw [h1]
  ring

theorem main (q m k : ℕ) (hq : 2 ≤ q) : ∀ (s : ℕ) (S : Finset (Fin m → Fin q)), S.card = s →
    k * (∑ x ∈ S, ∑ u ∈ S, if hd x u = 1 then 1 else 0)
      ≤ k * (3 * q + 2 * k) * S.card + ∑ x ∈ S, ∑ u ∈ S, if 3 ≤ hd x u then 1 else 0 := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro S hS
  classical
  by_cases hlow : ∀ x ∈ S, (∑ u ∈ S, if hd x u = 1 then 1 else 0) ≤ 3 * q + 2 * k
  · have h1 : ∑ x ∈ S, ∑ u ∈ S, (if hd x u = 1 then 1 else 0) ≤ S.card * (3 * q + 2 * k) := by
      calc ∑ x ∈ S, ∑ u ∈ S, (if hd x u = 1 then 1 else 0)
          ≤ ∑ _x ∈ S, (3 * q + 2 * k) := Finset.sum_le_sum hlow
        _ = S.card * (3 * q + 2 * k) := by simp
    calc k * (∑ x ∈ S, ∑ u ∈ S, if hd x u = 1 then 1 else 0)
        ≤ k * (S.card * (3 * q + 2 * k)) := Nat.mul_le_mul_left _ h1
      _ = k * (3 * q + 2 * k) * S.card := by ring
      _ ≤ _ := Nat.le_add_right _ _
  · obtain ⟨c, hcS, hc⟩ : ∃ c ∈ S, 3 * q + 2 * k < ∑ u ∈ S, if hd c u = 1 then 1 else 0 := by
      by_contra h
      apply hlow
      intro x hx
      by_contra h'
      exact h ⟨x, hx, not_le.1 h'⟩
    obtain ⟨N, hNdef⟩ : ∃ N : Finset (Fin m → Fin q), N = S.filter (fun u => hd c u = 1) := ⟨_, rfl⟩
    have hND : N.card = ∑ u ∈ S, if hd c u = 1 then 1 else 0 := by
      rw [hNdef]
      exact Finset.card_filter _ _
    have hNadj : ∀ u ∈ N, hd c u = 1 := by
      intro u hu
      rw [hNdef] at hu
      exact (Finset.mem_filter.1 hu).2
    have hNS : N ⊆ S := by
      rw [hNdef]
      exact Finset.filter_subset _ _
    have hcN : c ∉ N := by
      intro h
      have h1 := hNadj c h
      rw [hd_self] at h1
      omega
    obtain ⟨R, hRdef⟩ : ∃ R : Finset (Fin m → Fin q), R = insert c N := ⟨_, rfl⟩
    have hRS : R ⊆ S := by
      rw [hRdef]
      intro u hu
      rcases Finset.mem_insert.1 hu with h | h
      · rw [h]
        exact hcS
      · exact hNS h
    have hRcard : R.card = N.card + 1 := by
      rw [hRdef, Finset.card_insert_of_notMem hcN]
    have hdisj : Disjoint (S \ R) R := Finset.sdiff_disjoint
    have hunion : (S \ R) ∪ R = S := Finset.sdiff_union_of_subset hRS
    have hcard : S.card = (S \ R).card + R.card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have ihS' := ih (S \ R).card (by omega) (S \ R) rfl
    have eqE := split (fun x u : (Fin m → Fin q) => if hd x u = 1 then 1 else 0)
      (fun x u => by rw [hd_comm]) (S \ R) R hdisj
    have eqF := split (fun x u : (Fin m → Fin q) => if 3 ≤ hd x u then 1 else 0)
      (fun x u => by rw [hd_comm]) (S \ R) R hdisj
    rw [hunion] at eqE eqF
    have hRR : ∑ x ∈ R, ∑ u ∈ R, (if hd x u = 1 then 1 else 0) ≤ (3 * q + 2 * k) * R.card := by
      have h1 : ∀ x ∈ R, (∑ u ∈ R, if hd x u = 1 then 1 else 0)
          ≤ if x = c then R.card else 1 + q := by
        intro x hx
        by_cases hxc : x = c
        · simp only [hxc, ↓reduceIte]
          calc (∑ u ∈ R, if hd c u = 1 then 1 else 0) ≤ ∑ _u ∈ R, 1 :=
                Finset.sum_le_sum (fun u _ => by split_ifs <;> omega)
            _ = R.card := by simp
        · simp only [hxc, ↓reduceIte]
          have hxN : x ∈ N := by
            rw [hRdef] at hx
            rcases Finset.mem_insert.1 hx with h | h
            · exact absurd h hxc
            · exact h
          rw [hRdef, Finset.sum_insert hcN]
          have h2 : (∑ u ∈ N, if hd x u = 1 then 1 else 0) ≤ q := by
            rw [← Finset.card_filter]
            exact adj_common N hNadj (hNadj x hxN)
          have h3 : (if hd x c = 1 then 1 else 0) ≤ 1 := by split_ifs <;> omega
          omega
      have h2 : ∑ x ∈ R, (if x = c then R.card else 1 + q) = R.card + N.card * (1 + q) := by
        rw [hRdef, Finset.sum_insert hcN]
        simp only [↓reduceIte]
        have h3 : ∀ x ∈ N, (if x = c then (insert c N).card else 1 + q) = 1 + q := by
          intro x hx
          have hxc : x ≠ c := by
            rintro rfl
            exact hcN hx
          simp [hxc]
        rw [Finset.sum_congr rfl h3]
        simp
      have h3 := Finset.sum_le_sum h1
      rw [h2] at h3
      have h4 : 2 * N.card ≤ q * N.card := Nat.mul_le_mul_right _ hq
      nlinarith
    have hcross : ∀ x ∈ S \ R, k * (∑ u ∈ R, if hd x u = 1 then 1 else 0)
        ≤ ∑ u ∈ R, if 3 ≤ hd x u then 1 else 0 := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      have hxc : x ≠ c := by
        intro h
        apply hx.2
        rw [hRdef, h]
        exact Finset.mem_insert_self _ _
      have hxN : hd c x ≠ 1 := by
        intro h
        apply hx.2
        rw [hRdef, hNdef]
        exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hx.1, h⟩)
      have hxc1 : hd x c ≠ 1 := by
        rw [hd_comm]
        exact hxN
      have e1 : (∑ u ∈ R, if hd x u = 1 then 1 else 0)
          = (N.filter (fun u => hd x u = 1)).card := by
        rw [hRdef, Finset.sum_insert hcN, Finset.card_filter]
        simp [hxc1]
      have e2 : (N.filter (fun u => 3 ≤ hd x u)).card
          ≤ ∑ u ∈ R, if 3 ≤ hd x u then 1 else 0 := by
        rw [hRdef, Finset.sum_insert hcN, Finset.card_filter]
        exact Nat.le_add_left _ _
      rw [e1]
      rcases Nat.eq_zero_or_pos (N.filter (fun u => hd x u = 1)).card with h0 | hpos
      · rw [h0]
        simp
      · obtain ⟨u0, hu0⟩ := Finset.card_pos.1 hpos
        rw [Finset.mem_filter] at hu0
        have ht := hd_tri c u0 x
        have h1 := hNadj u0 hu0.1
        have h2 : hd u0 x = 1 := by
          rw [hd_comm]
          exact hu0.2
        have h3 : hd c x ≠ 0 := by
          intro h
          exact hxc (hd_eq_zero h).symm
        have hcx : hd c x = 2 := by omega
        obtain ⟨t1, t2⟩ := two_away N hNadj hcx
        have h4 := Finset.card_filter_add_card_filter_not (s := N) (fun u => 3 ≤ hd x u)
        have h5 : (N.filter (fun u => ¬ 3 ≤ hd x u)) = N.filter (fun u => hd x u ≤ 2) := by
          apply Finset.filter_congr
          intro u _
          omega
        rw [h5] at h4
        have h6 : k * (N.filter (fun u => hd x u = 1)).card ≤ k * 2 :=
          Nat.mul_le_mul_left _ t2
        omega
    have hX : k * (∑ x ∈ S \ R, ∑ u ∈ R, if hd x u = 1 then 1 else 0)
        ≤ ∑ x ∈ S \ R, ∑ u ∈ R, if 3 ≤ hd x u then 1 else 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hcross
    have hRR' : k * (∑ x ∈ R, ∑ u ∈ R, if hd x u = 1 then 1 else 0)
        ≤ k * ((3 * q + 2 * k) * R.card) := Nat.mul_le_mul_left _ hRR
    rw [eqE, eqF, hcard]
    generalize (∑ x ∈ S \ R, ∑ u ∈ S \ R, if hd x u = 1 then 1 else 0) = a1 at ihS' ⊢
    generalize (∑ x ∈ S \ R, ∑ u ∈ R, if hd x u = 1 then 1 else 0) = a2 at hX ⊢
    generalize (∑ x ∈ R, ∑ u ∈ R, if hd x u = 1 then 1 else 0) = a3 at hRR' ⊢
    generalize (∑ x ∈ S \ R, ∑ u ∈ S \ R, if 3 ≤ hd x u then 1 else 0) = b1 at ihS' ⊢
    generalize (∑ x ∈ S \ R, ∑ u ∈ R, if 3 ≤ hd x u then 1 else 0) = b2 at hX ⊢
    generalize (∑ x ∈ R, ∑ u ∈ R, if 3 ≤ hd x u then 1 else 0) = b3
    have e1 : k * (a1 + 2 * a2 + a3) = k * a1 + 2 * (k * a2) + k * a3 := by ring
    have e2 : k * (3 * q + 2 * k) * ((S \ R).card + R.card)
        = k * (3 * q + 2 * k) * (S \ R).card + k * ((3 * q + 2 * k) * R.card) := by ring
    rw [e1, e2]
    linarith

end PEqualNP.Outside.L_lib_1000

theorem PEqualNP.Outside.L_lib_1000 : (∀ (q m k : Nat), 2 ≤ q → 0 < k →
  let W := Fin m → Fin q
  let dist := fun (x y : W) =>
    ((Finset.univ : Finset (Fin m)).filter (fun i => x i ≠ y i)).card
  ∀ S : Finset W,
    let pairs := S.product S
    let edges := (pairs.filter (fun p => dist p.1 p.2 = 1)).card
    let far := (pairs.filter (fun p => 3 ≤ dist p.1 p.2)).card
    k * edges ≤ k * (3*q + 2*k) * S.card + far) := by
  intro q m k hq hk W dist S pairs edges far
  have h := PEqualNP.Outside.L_lib_1000.main q m k hq S.card S rfl
  have e1 : edges = ∑ x ∈ S, ∑ u ∈ S, if PEqualNP.Outside.L_lib_1000.hd x u = 1 then 1 else 0 := by
    show ((S ×ˢ S).filter (fun p => PEqualNP.Outside.L_lib_1000.hd p.1 p.2 = 1)).card = _
    rw [Finset.card_filter, Finset.sum_product]
  have e2 : far = ∑ x ∈ S, ∑ u ∈ S, if 3 ≤ PEqualNP.Outside.L_lib_1000.hd x u then 1 else 0 := by
    show ((S ×ˢ S).filter (fun p => 3 ≤ PEqualNP.Outside.L_lib_1000.hd p.1 p.2)).card = _
    rw [Finset.card_filter, Finset.sum_product]
  rw [e1, e2]
  exact h
