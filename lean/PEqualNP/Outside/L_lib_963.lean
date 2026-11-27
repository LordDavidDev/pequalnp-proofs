import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_963

def gaps : ℝ → List ℝ → List (ℝ × ℝ)
  | _, [] => []
  | b, a :: l => (a - b, a) :: gaps a l

noncomputable def gS (c : ℝ) (comps : List (ℝ × ℝ)) : ℝ :=
  (comps.map (fun p => if p.2 ≤ c then p.1 else 0)).sum

theorem gS_nil (c : ℝ) : gS c [] = 0 := rfl

theorem gS_cons (c : ℝ) (p : ℝ × ℝ) (r : List (ℝ × ℝ)) :
    gS c (p :: r) = (if p.2 ≤ c then p.1 else 0) + gS c r := rfl

theorem gaps_mem : ∀ (l : List ℝ) (b : ℝ), List.Pairwise (· ≤ ·) (b :: l) →
    ∀ p ∈ gaps b l, 0 ≤ p.1 ∧ p.2 ∈ l := by
  intro l
  induction l with
  | nil =>
    intro b _ p hp
    simp [gaps] at hp
  | cons a l ih =>
    intro b hb p hp
    rw [List.pairwise_cons] at hb
    simp only [gaps, List.mem_cons] at hp
    rcases hp with hp | hp
    · rw [hp]
      exact ⟨sub_nonneg.2 (hb.1 a (List.mem_cons_self ..)), List.mem_cons_self ..⟩
    · obtain ⟨h1, h2⟩ := ih a hb.2 p hp
      exact ⟨h1, List.mem_cons_of_mem _ h2⟩

theorem gS_bounds (c : ℝ) : ∀ comps : List (ℝ × ℝ), (∀ p ∈ comps, 0 ≤ p.1) →
    0 ≤ gS c comps ∧ gS c comps ≤ (comps.map Prod.fst).sum := by
  intro comps
  induction comps with
  | nil =>
    intro _
    simp [gS]
  | cons p r ih =>
    intro h
    obtain ⟨h1, h2⟩ := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
    have hp := h p (List.mem_cons_self ..)
    rw [gS_cons, List.map_cons, List.sum_cons]
    constructor
    · split_ifs <;> linarith
    · split_ifs <;> linarith

theorem gS_le : ∀ (l : List ℝ) (b c : ℝ), List.Pairwise (· ≤ ·) (b :: l) →
    gS c (gaps b l) ≤ max (c - b) 0 := by
  intro l
  induction l with
  | nil =>
    intro b c _
    simp [gaps, gS]
  | cons a l ih =>
    intro b c hb
    rw [List.pairwise_cons] at hb
    have h1 := ih a c hb.2
    simp only [gaps]
    rw [gS_cons]
    by_cases h : a ≤ c
    · simp only [h, ↓reduceIte]
      rw [max_eq_left (sub_nonneg.2 h)] at h1
      linarith [le_max_left (c - b) 0]
    · simp only [h, ↓reduceIte]
      rw [max_eq_right (by linarith)] at h1
      linarith [le_max_right (c - b) 0]

theorem gS_eq : ∀ (l : List ℝ) (b c : ℝ), List.Pairwise (· ≤ ·) (b :: l) → c ∈ l →
    gS c (gaps b l) = c - b := by
  intro l
  induction l with
  | nil =>
    intro b c _ hc
    simp at hc
  | cons a l ih =>
    intro b c hb hc
    rw [List.pairwise_cons] at hb
    simp only [gaps]
    rw [gS_cons]
    rcases List.mem_cons.1 hc with hca | hcl
    · rw [hca]
      simp only [le_refl, ↓reduceIte]
      have h1 := gS_le l a a hb.2
      rw [sub_self, max_self] at h1
      have h2 := (gS_bounds a (gaps a l) (fun p hp => (gaps_mem l a hb.2 p hp).1)).1
      linarith
    · have hac : a ≤ c := (List.pairwise_cons.1 hb.2).1 c hcl
      simp only [hac, ↓reduceIte]
      rw [ih a c hb.2 hcl]
      ring

theorem gS_total : ∀ (l : List ℝ) (b c : ℝ), (∀ a ∈ l, a ≤ c) →
    gS c (gaps b l) = ((gaps b l).map Prod.fst).sum := by
  intro l
  induction l with
  | nil =>
    intro b c _
    simp [gaps, gS]
  | cons a l ih =>
    intro b c h
    simp only [gaps]
    rw [gS_cons, List.map_cons, List.sum_cons, ih a c (fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))]
    have hac : a ≤ c := h a (List.mem_cons_self ..)
    simp only [hac, ↓reduceIte]

theorem layer (G : Finset ℝ) (m : ℝ) (hm : 0 ≤ m) (hG : ∀ a ∈ G, 0 < a ∧ a ≤ m) :
    ∃ comps : List (ℝ × ℝ), (∀ p ∈ comps, 0 ≤ p.1 ∧ 0 < p.2 ∧ p.2 ≤ m) ∧
      (comps.map Prod.fst).sum = m ∧ (∀ c, 0 ≤ c → gS c comps ≤ c) ∧
      (∀ c ∈ G, gS c comps = c) := by
  rcases hm.eq_or_lt with h0 | hpos
  · refine ⟨[], ?_, ?_, ?_, ?_⟩
    · intro p hp
      simp at hp
    · simp [h0]
    · intro c hc
      rw [gS_nil]
      exact hc
    · intro c hc
      have h1 := hG c hc
      linarith
  · have hl : ∀ a ∈ (insert m G).sort (· ≤ ·), 0 < a ∧ a ≤ m := by
      intro a ha
      rw [Finset.mem_sort, Finset.mem_insert] at ha
      rcases ha with ha | ha
      · rw [ha]
        exact ⟨hpos, le_refl _⟩
      · exact hG a ha
    have hpw : List.Pairwise (· ≤ ·) (0 :: (insert m G).sort (· ≤ ·)) :=
      List.pairwise_cons.2 ⟨fun a ha => (hl a ha).1.le, Finset.pairwise_sort _ _⟩
    refine ⟨gaps 0 ((insert m G).sort (· ≤ ·)), ?_, ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨h1, h2⟩ := gaps_mem _ 0 hpw p hp
      exact ⟨h1, hl _ h2⟩
    · rw [← gS_total _ 0 m (fun a ha => (hl a ha).2),
        gS_eq _ 0 m hpw (by rw [Finset.mem_sort]; exact Finset.mem_insert_self _ _), sub_zero]
    · intro c hc
      have h1 := gS_le _ 0 c hpw
      rw [sub_zero, max_eq_left hc] at h1
      exact h1
    · intro c hc
      rw [gS_eq _ 0 c hpw (by rw [Finset.mem_sort]; exact Finset.mem_insert_of_mem hc), sub_zero]

theorem sum_sub_form (c : ℝ) : ∀ comps : List (ℝ × ℝ),
    (comps.map (fun p => 2 * p.1 - (if p.2 ≤ c then p.1 else 0))).sum
      = 2 * (comps.map Prod.fst).sum - gS c comps := by
  intro comps
  induction comps with
  | nil => simp [gS]
  | cons p r ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, gS_cons]
    ring

theorem sum_add_form (c : ℝ) : ∀ comps : List (ℝ × ℝ),
    (comps.map (fun p => 2 * p.1 + (if p.2 ≤ c then p.1 else 0))).sum
      = 2 * (comps.map Prod.fst).sum + gS c comps := by
  intro comps
  induction comps with
  | nil => simp [gS]
  | cons p r ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, gS_cons]
    ring

theorem sum_get {α : Type} (l : List α) (F : α → ℝ) :
    ∑ i : Fin l.length, F (l.get i) = (l.map F).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ← ih]
    exact Fin.sum_univ_succ (fun i : Fin (l.length + 1) => F ((a :: l).get i))

def nbr {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (I : Finset (Fin n)) :
    Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun v => ∃ u ∈ I, G.Adj u v)

noncomputable def optA {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I : Finset (Fin n)) : Fin n → ℝ :=
  fun u => if u ∈ I then 1/2 else if u ∈ nbr G I then 3/2 else 1

noncomputable def optB {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) : Fin n → ℝ :=
  fun u => if u = v then 0 else if G.Adj v u then 2 else 1

def isOpt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℝ) : Prop :=
  (∃ I : Finset (Fin n), (∀ u ∈ I, ∀ v ∈ I, ¬G.Adj u v) ∧ ∀ u,
    x u = if u ∈ I then 1/2 else if u ∈ nbr G I then 3/2 else 1) ∨
  ∃ v : Fin n, ∀ u, x u = if u = v then 0 else if G.Adj v u then 2 else 1

def isBlock {n : ℕ} (G : SimpleGraph (Fin n)) (y : Fin n → ℝ) : Prop :=
  (∀ u, 0 ≤ y u) ∧ (∀ u v, u ≠ v → 1 ≤ y u + y v) ∧ ∀ u v, G.Adj u v → 2 ≤ y u + y v

theorem opt_block {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℝ)
    (hx : isOpt G x) : isBlock G x := by
  rcases hx with ⟨I, hI, hx⟩ | ⟨v0, hx⟩
  · have hge : ∀ u, 1/2 ≤ x u := by
      intro u
      rw [hx u]
      split_ifs <;> norm_num
    have hge1 : ∀ u, u ∉ I → 1 ≤ x u := by
      intro u hu
      rw [hx u]
      simp only [hu, ↓reduceIte]
      split_ifs <;> norm_num
    have hadj : ∀ u v, u ∈ I → G.Adj u v → x u + x v = 2 := by
      intro u v hu huv
      have hv : v ∉ I := fun hv => hI u hu v hv huv
      have hvn : v ∈ nbr G I := Finset.mem_filter.2 ⟨Finset.mem_univ _, u, hu, huv⟩
      rw [hx u, hx v]
      simp only [hu, hv, hvn, ↓reduceIte]
      norm_num
    refine ⟨fun u => by linarith [hge u], fun u v _ => by linarith [hge u, hge v], ?_⟩
    intro u v huv
    by_cases hu : u ∈ I
    · linarith [hadj u v hu huv]
    · by_cases hv : v ∈ I
      · linarith [hadj v u hv huv.symm]
      · linarith [hge1 u hu, hge1 v hv]
  · have hge : ∀ u, 0 ≤ x u := by
      intro u
      rw [hx u]
      split_ifs <;> norm_num
    have hge1 : ∀ u, u ≠ v0 → 1 ≤ x u := by
      intro u hu
      rw [hx u]
      simp only [hu, ↓reduceIte]
      split_ifs <;> norm_num
    have hadj : ∀ u, G.Adj v0 u → x u = 2 := by
      intro u hu
      have hne : u ≠ v0 := fun h => G.loopless.irrefl v0 (h ▸ hu)
      rw [hx u]
      simp only [hne, hu, ↓reduceIte]
    refine ⟨hge, ?_, ?_⟩
    · intro u v huv
      by_cases hu : u = v0
      · have hv : v ≠ v0 := fun h => huv (hu.trans h.symm)
        linarith [hge u, hge1 v hv]
      · linarith [hge1 u hu, hge v]
    · intro u v huv
      by_cases hu : u = v0
      · rw [hu] at huv
        linarith [hge u, hadj v huv]
      · by_cases hv : v = v0
        · rw [hv] at huv
          linarith [hge v, hadj u huv.symm]
        · linarith [hge1 u hu, hge1 v hv]

theorem mix_block {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (y : Fin n → ℝ)
    (k : ℕ) (w : Fin k → ℝ) (x : Fin k → Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i ∧ isOpt G (x i)) (hsum : (∑ i, w i) = 1)
    (hle : ∀ u, (∑ i, w i * x i u) ≤ y u) : isBlock G y := by
  have hb : ∀ i, isBlock G (x i) := fun i => opt_block G (x i) (hw i).2
  refine ⟨?_, ?_, ?_⟩
  · intro u
    refine le_trans ?_ (hle u)
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i).1 ((hb i).1 u))
  · intro u v huv
    have h1 : (∑ i, w i * 1) ≤ ∑ i, (w i * x i u + w i * x i v) := by
      apply Finset.sum_le_sum
      intro i _
      have h2 := (hb i).2.1 u v huv
      nlinarith [(hw i).1]
    rw [Finset.sum_add_distrib] at h1
    simp only [mul_one] at h1
    linarith [hle u, hle v]
  · intro u v huv
    have h1 : (∑ i, w i * 2) ≤ ∑ i, (w i * x i u + w i * x i v) := by
      apply Finset.sum_le_sum
      intro i _
      have h2 := (hb i).2.2 u v huv
      nlinarith [(hw i).1]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul] at h1
    linarith [hle u, hle v]

theorem core {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (z : Fin n → ℝ)
    (hz : isBlock G z) (m : ℝ) (hm0 : 0 ≤ m) (hm : m ≤ 1/2) (xB : Fin n → ℝ)
    (hxB : isOpt G xB)
    (hg : ∀ u, z u < 1 → min (z u) (1 - z u) ≤ m)
    (hB2 : ∀ u, z u < 1 → (1 - 2 * m) * xB u + 2 * m - min (z u) (1 - z u) ≤ z u)
    (hB3 : ∀ u, 1 ≤ z u → (1 - 2 * m) * xB u + 2 * m + min (z u - 1) m ≤ z u) :
    ∃ ML : List (ℝ × (Fin n → ℝ)), (∀ p ∈ ML, 0 ≤ p.1 ∧ isOpt G p.2) ∧
      (ML.map Prod.fst).sum = 1 ∧ ∀ u, (ML.map (fun p => p.1 * p.2 u)).sum ≤ z u := by
  classical
  have hg0 : ∀ u, z u < 1 → 0 ≤ min (z u) (1 - z u) := by
    intro u hu
    exact le_min (hz.1 u) (by linarith)
  obtain ⟨comps, hc1, hc2, hc3, hc4⟩ := layer
    (((Finset.univ.filter (fun u => z u < 1)).image
      (fun u => min (z u) (1 - z u))).filter (fun a => 0 < a)) m hm0 (by
      intro a ha
      rw [Finset.mem_filter, Finset.mem_image] at ha
      obtain ⟨⟨u, hu, rfl⟩, hpos⟩ := ha
      exact ⟨hpos, hg u (Finset.mem_filter.1 hu).2⟩)
  have hw0 : ∀ p ∈ comps, 0 ≤ p.1 := fun p hp => (hc1 p hp).1
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ → Finset (Fin n), ∀ τ u,
      u ∈ I τ ↔ (z u < 1 ∧ τ ≤ min (z u) (1 - z u)) :=
    ⟨fun τ => Finset.univ.filter (fun u => z u < 1 ∧ τ ≤ min (z u) (1 - z u)), by
      intro τ u
      simp⟩
  have hI : ∀ τ, ∀ u ∈ I τ, ∀ v ∈ I τ, ¬G.Adj u v := by
    intro τ u hu v hv hadj
    have h1 := hz.2.2 u v hadj
    have h2 := ((hIdef τ u).1 hu).1
    have h3 := ((hIdef τ v).1 hv).1
    linarith
  have hval1 : ∀ τ u, z u < 1 →
      optA G (I τ) u ≤ 1 - (if τ ≤ min (z u) (1 - z u) then 1/2 else 0) := by
    intro τ u hu
    unfold optA
    by_cases huI : u ∈ I τ
    · have h2 := ((hIdef τ u).1 huI).2
      simp only [huI, h2, ↓reduceIte]
      norm_num
    · have h2 : ¬ τ ≤ min (z u) (1 - z u) := fun h => huI ((hIdef τ u).2 ⟨hu, h⟩)
      have hn : u ∉ nbr G (I τ) := by
        intro hn
        obtain ⟨w, hw, hadj⟩ := (Finset.mem_filter.1 hn).2
        have h3 := hz.2.2 w u hadj
        have h4 := ((hIdef τ w).1 hw).1
        linarith
      simp only [huI, hn, h2, ↓reduceIte]
      norm_num
  have hval2 : ∀ τ u, 0 < τ → 1 ≤ z u →
      optA G (I τ) u ≤ 1 + (if τ ≤ z u - 1 then 1/2 else 0) := by
    intro τ u hτ hu
    unfold optA
    have huI : u ∉ I τ := by
      intro h
      have h2 := ((hIdef τ u).1 h).1
      linarith
    by_cases hn : u ∈ nbr G (I τ)
    · obtain ⟨w, hw, hadj⟩ := (Finset.mem_filter.1 hn).2
      have h3 := hz.2.2 w u hadj
      have h4 := ((hIdef τ w).1 hw).2
      have h5 : min (z w) (1 - z w) ≤ 1 - z w := min_le_right _ _
      have h6 : τ ≤ z u - 1 := by linarith
      simp only [huI, hn, h6, ↓reduceIte]
      norm_num
    · simp only [huI, hn, ↓reduceIte]
      split_ifs <;> norm_num
  refine ⟨(1 - 2 * m, xB) :: comps.map (fun p => (2 * p.1, optA G (I p.2))), ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_cons.1 hp with hp | hp
    · rw [hp]
      exact ⟨by linarith, hxB⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact ⟨by linarith [hw0 q hq], Or.inl ⟨I q.2, hI q.2, fun u => rfl⟩⟩
  · rw [List.map_cons, List.sum_cons, List.map_map]
    have h1 : (comps.map (Prod.fst ∘ fun p : ℝ × ℝ => (2 * p.1, optA G (I p.2)))).sum
        = 2 * (comps.map Prod.fst).sum := by
      rw [← List.sum_map_mul_left]
      rfl
    rw [h1, hc2]
    ring
  · intro u
    rw [List.map_cons, List.sum_cons, List.map_map]
    by_cases hu : z u < 1
    · have h1 : (comps.map ((fun p : ℝ × (Fin n → ℝ) => p.1 * p.2 u) ∘
          fun p : ℝ × ℝ => (2 * p.1, optA G (I p.2)))).sum
          ≤ (comps.map (fun p : ℝ × ℝ =>
            2 * p.1 - (if p.2 ≤ min (z u) (1 - z u) then p.1 else 0))).sum := by
        apply List.sum_le_sum
        intro p hp
        have h2 := hval1 p.2 u hu
        have h3 := hw0 p hp
        show 2 * p.1 * optA G (I p.2) u ≤ _
        split_ifs at h2 ⊢ <;> nlinarith
      rw [sum_sub_form, hc2] at h1
      have h4 : gS (min (z u) (1 - z u)) comps = min (z u) (1 - z u) := by
        rcases (hg0 u hu).eq_or_lt with h0 | hpos
        · rw [← h0]
          have h5 := hc3 0 (le_refl _)
          have h6 := (gS_bounds 0 comps hw0).1
          linarith
        · apply hc4
          rw [Finset.mem_filter, Finset.mem_image]
          exact ⟨⟨u, Finset.mem_filter.2 ⟨Finset.mem_univ _, hu⟩, rfl⟩, hpos⟩
      rw [h4] at h1
      have h7 := hB2 u hu
      show (1 - 2 * m) * xB u + _ ≤ z u
      linarith
    · have hu1 : 1 ≤ z u := not_lt.1 hu
      have h1 : (comps.map ((fun p : ℝ × (Fin n → ℝ) => p.1 * p.2 u) ∘
          fun p : ℝ × ℝ => (2 * p.1, optA G (I p.2)))).sum
          ≤ (comps.map (fun p : ℝ × ℝ =>
            2 * p.1 + (if p.2 ≤ z u - 1 then p.1 else 0))).sum := by
        apply List.sum_le_sum
        intro p hp
        have h2 := hval2 p.2 u (hc1 p hp).2.1 hu1
        have h3 := hw0 p hp
        show 2 * p.1 * optA G (I p.2) u ≤ _
        split_ifs at h2 ⊢ <;> nlinarith
      rw [sum_add_form, hc2] at h1
      have h4 := hc3 (z u - 1) (by linarith)
      have h5 := (gS_bounds (z u - 1) comps hw0).2
      rw [hc2] at h5
      have h6 : gS (z u - 1) comps ≤ min (z u - 1) m := le_min h4 h5
      have h7 := hB3 u hu1
      show (1 - 2 * m) * xB u + _ ≤ z u
      linarith

theorem block_mix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (y : Fin n → ℝ)
    (hy : isBlock G y) :
    ∃ (k : ℕ) (w : Fin k → ℝ) (x : Fin k → Fin n → ℝ),
      (∀ i, 0 ≤ w i ∧ isOpt G (x i)) ∧ (∑ i, w i) = 1 ∧
      ∀ u, (∑ i, w i * x i u) ≤ y u := by
  classical
  obtain ⟨z, hzdef⟩ : ∃ z : Fin n → ℝ, ∀ u, z u = min (y u) 2 := ⟨_, fun _ => rfl⟩
  have hzy : ∀ u, z u ≤ y u := by
    intro u
    rw [hzdef]
    exact min_le_left _ _
  have hz0 : ∀ u, 0 ≤ z u := by
    intro u
    rw [hzdef]
    exact le_min (hy.1 u) (by norm_num)
  have hz : isBlock G z := by
    refine ⟨hz0, ?_, ?_⟩
    · intro u v huv
      have h1 := hy.2.1 u v huv
      have h2 := hz0 u
      have h3 := hz0 v
      rw [hzdef] at h2 h3 ⊢
      rw [hzdef v]
      rcases min_cases (y u) 2 with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
        rcases min_cases (y v) 2 with ⟨e2, _⟩ | ⟨e2, _⟩ <;> rw [e1, e2] <;>
          linarith [hy.1 u, hy.1 v]
    · intro u v huv
      have h1 := hy.2.2 u v huv
      have h2 := hz0 u
      have h3 := hz0 v
      rw [hzdef] at h2 h3 ⊢
      rw [hzdef v]
      rcases min_cases (y u) 2 with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
        rcases min_cases (y v) 2 with ⟨e2, _⟩ | ⟨e2, _⟩ <;> rw [e1, e2] <;>
          linarith [hy.1 u, hy.1 v]
  have hfin : ∃ ML : List (ℝ × (Fin n → ℝ)), (∀ p ∈ ML, 0 ≤ p.1 ∧ isOpt G p.2) ∧
      (ML.map Prod.fst).sum = 1 ∧ ∀ u, (ML.map (fun p => p.1 * p.2 u)).sum ≤ z u := by
    by_cases hex : ∃ v0, z v0 < 1/2
    · obtain ⟨v0, hv0⟩ := hex
      have hpair : ∀ u, u ≠ v0 → 1 - z v0 ≤ z u := by
        intro u hu
        have h1 := hz.2.1 u v0 hu
        linarith
      have hnadj : ∀ u, z u < 1 → ¬ G.Adj v0 u := by
        intro u hu hadj
        have h1 := hz.2.2 v0 u hadj
        linarith
      have hBv0 : optB G v0 v0 = 0 := by simp [optB]
      have hB1 : ∀ u, u ≠ v0 → ¬ G.Adj v0 u → optB G v0 u = 1 := by
        intro u hu hadj
        simp [optB, hu, hadj]
      have hB2' : ∀ u, optB G v0 u ≤ 2 := by
        intro u
        unfold optB
        split_ifs <;> norm_num
      apply core G z hz (z v0) (hz0 v0) hv0.le (optB G v0) (Or.inr ⟨v0, fun u => rfl⟩)
      · intro u hu
        by_cases huv : u = v0
        · rw [huv]
          exact min_le_left _ _
        · have h1 := hpair u huv
          have h2 : min (z u) (1 - z u) ≤ 1 - z u := min_le_right _ _
          linarith
      · intro u hu
        by_cases huv : u = v0
        · rw [huv, hBv0, min_eq_left (by linarith)]
          linarith
        · have h1 := hpair u huv
          rw [hB1 u huv (hnadj u hu), min_eq_right (by linarith)]
          linarith
      · intro u hu
        have huv : u ≠ v0 := by
          rintro rfl
          linarith
        by_cases hadj : G.Adj v0 u
        · have h1 := hz.2.2 v0 u hadj
          have h2 := hB2' u
          have h3 : min (z u - 1) (z v0) ≤ z v0 := min_le_right _ _
          nlinarith [hz0 v0]
        · rw [hB1 u huv hadj]
          have h3 : min (z u - 1) (z v0) ≤ z u - 1 := min_le_left _ _
          linarith
    · have hhalf : ∀ u, 1/2 ≤ z u := by
        intro u
        by_contra h
        exact hex ⟨u, not_le.1 h⟩
      apply core G z hz (1/2) (by norm_num) (le_refl _) (optA G ∅)
        (Or.inl ⟨∅, by simp, fun u => rfl⟩)
      · intro u hu
        have h2 : min (z u) (1 - z u) ≤ 1 - z u := min_le_right _ _
        linarith [hhalf u]
      · intro u hu
        rw [min_eq_right (by linarith [hhalf u])]
        norm_num
      · intro u hu
        have h3 : min (z u - 1) (1/2) ≤ z u - 1 := min_le_left _ _
        norm_num
        linarith
  obtain ⟨ML, h1, h2, h3⟩ := hfin
  refine ⟨ML.length, fun i => (ML.get i).1, fun i => (ML.get i).2, ?_, ?_, ?_⟩
  · intro i
    exact h1 _ (List.get_mem ML i)
  · rw [sum_get ML (fun p => p.1)]
    exact h2
  · intro u
    rw [sum_get ML (fun p => p.1 * p.2 u)]
    exact le_trans (h3 u) (hzy u)

end PEqualNP.Outside.L_lib_963

theorem PEqualNP.Outside.L_lib_963 : (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
  let V := Fin n
  let nbr := fun (I : Finset V) =>
    (Finset.univ : Finset V).filter (fun v => ∃ u ∈ I, G.Adj u v)
  let indep := fun (I : Finset V) => ∀ u ∈ I, ∀ v ∈ I, ¬G.Adj u v
  let block := fun (y : V → ℝ) => (∀ u, 0 ≤ y u) ∧
    (∀ u v, u ≠ v → 1 ≤ y u+y v) ∧ ∀ u v, G.Adj u v → 2 ≤ y u+y v
  let option := fun (x : V → ℝ) =>
    (∃ I : Finset V, indep I ∧ ∀ u,
      x u = if u ∈ I then 1/2 else if u ∈ nbr I then 3/2 else 1) ∨
    ∃ v : V, ∀ u, x u = if u = v then 0 else if G.Adj v u then 2 else 1
  (∀ x : V → ℝ, option x → block x) ∧
  ∀ y : V → ℝ, block y ↔
    ∃ (m : ℕ) (w : Fin m → ℝ) (x : Fin m → V → ℝ),
      (∀ i, 0 ≤ w i ∧ option (x i)) ∧ (∑ i, w i) = 1 ∧
      ∀ u, (∑ i, w i * x i u) ≤ y u) := by
  intro n G _ V nbr indep block option
  refine ⟨fun x hx => PEqualNP.Outside.L_lib_963.opt_block G x hx, fun y => ⟨?_, ?_⟩⟩
  · intro hy
    exact PEqualNP.Outside.L_lib_963.block_mix G y hy
  · rintro ⟨k, w, x, hw, hsum, hle⟩
    exact PEqualNP.Outside.L_lib_963.mix_block G y k w x hw hsum hle
