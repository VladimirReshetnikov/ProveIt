import IntegerPoints.KuzminLandau

/-!
# The van der Corput second-derivative test

For `f ∈ C²` with `λ₂ ≤ f'' ≤ α λ₂` on `[A+1, B]` (`0 < λ₂`), one has
`‖∑_{A < n ≤ B} e(f(n))‖ ≤ 12 α (B - A) λ₂^{1/2} + 24 λ₂^{-1/2}`.

The proof is the classical one: `f'` is increasing, so the integers
`n ∈ (A, B]` split into consecutive *windows* on which `round(f'(n))` is a
fixed integer `m`.  Inside a window, with `δ = λ₂^{1/2}`, the integers with
`f'(n) ≤ m - δ` and those with `f'(n) ≥ m + δ` form initial and final
segments on which Kuz'min–Landau applies with `λ = δ`, while the middle
segment `|f'(n) - m| < δ` contains at most `2/δ + 1` integers because
consecutive values of `f'` differ by at least `λ₂ = δ²`.  Hence a window
costs at most `10/δ + 1`, and there are at most `f'(B) - f'(A+1) + 2`
windows.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

namespace VdC

/-- If `x - k ∈ [δ, 1 - δ]` for an integer `k` then `‖x‖ ≥ δ`. -/
theorem nearestIntDist_ge {x δ : ℝ} (k : ℤ) (h1 : δ ≤ x - k) (h2 : x - k ≤ 1 - δ) :
    δ ≤ nearestIntDist x := by
  unfold nearestIntDist
  rcases le_or_gt (round x) k with h | h
  · have : (round x : ℝ) ≤ k := by exact_mod_cast h
    exact le_trans (by linarith) (le_abs_self (x - round x))
  · have : (k : ℝ) + 1 ≤ round x := by exact_mod_cast Int.add_one_le_iff.2 h
    exact le_trans (by linarith) (neg_le_abs (x - round x))

/-- A downward-closed subset of `(A, B]` is an initial segment. -/
theorem filter_eq_Ioc_of_downward (A B : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ n n', A < n → n ≤ n' → n' ≤ B → P n' → P n) :
    (Finset.Ioc A B).filter P = Finset.Ioc A (A + ((Finset.Ioc A B).filter P).card) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hPn⟩
    refine ⟨h1, ?_⟩
    have hsub : Finset.Ioc A n ⊆ (Finset.Ioc A B).filter P := by
      intro n' hn'
      rw [Finset.mem_Ioc] at hn'
      rw [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨hn'.1, by omega⟩, hP n' n hn'.1 hn'.2 h2 hPn⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Ioc] at this
    omega
  · rintro ⟨h1, h2⟩
    by_contra hcon
    have hcard := Finset.card_filter_le (Finset.Ioc A B) P
    rw [Nat.card_Ioc] at hcard
    have hnB : n ≤ B := by omega
    have hPn : ¬ P n := fun hPn => hcon ⟨⟨h1, hnB⟩, hPn⟩
    have hsub : (Finset.Ioc A B).filter P ⊆ Finset.Ioc A (n - 1) := by
      intro n' hn'
      rw [Finset.mem_filter, Finset.mem_Ioc] at hn'
      rw [Finset.mem_Ioc]
      refine ⟨hn'.1.1, ?_⟩
      by_contra h
      push Not at h
      exact hPn (hP n n' h1 (by omega) hn'.1.2 hn'.2)
    have := Finset.card_le_card hsub
    rw [Nat.card_Ioc] at this
    omega

variable (f : ℝ → ℝ)

/-- The bound for a single window: all `n ∈ (A, B]` have
`m - 1/2 ≤ f'(n) < m + 1/2`. -/
theorem window_bound (A B : ℕ) (m : ℤ) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hf : ContDiff ℝ 2 f)
    (hmono : MonotoneOn (deriv f) (Set.Icc (A + 1 : ℝ) B))
    (h2 : ∀ t ∈ Set.Icc (A + 1 : ℝ) B, δ ^ 2 ≤ deriv (deriv f) t)
    (hwin : ∀ n ∈ Finset.Ioc A B, (m : ℝ) - 1 / 2 ≤ deriv f n ∧ deriv f n < m + 1 / 2) :
    ‖∑ n ∈ Finset.Ioc A B, e (f n)‖ ≤ 10 / δ + 1 := by
  classical
  rcases Nat.lt_or_ge B A with hBA | hAB
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
    positivity
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hf' : ContDiff ℝ 1 (deriv f) := (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f from hf)).2.2
  have h4δ : 0 < 4 / δ := by positivity
  have h2δ : (1 : ℝ) ≤ 2 / δ := by
    rw [le_div_iff₀ hδ]
    linarith
  -- integer monotonicity
  have hmonoN : ∀ n n' : ℕ, A < n → n ≤ n' → n' ≤ B → deriv f n ≤ deriv f n' := by
    intro n n' h1 h12 h2
    apply hmono
    · exact ⟨by exact_mod_cast h1, by exact_mod_cast (le_trans h12 h2)⟩
    · exact ⟨by exact_mod_cast (lt_of_lt_of_le h1 h12), by exact_mod_cast h2⟩
    · exact_mod_cast h12
  -- the three segments
  set P₁ : ℕ → Prop := fun n => deriv f n ≤ m - δ with hP₁
  set P₂ : ℕ → Prop := fun n => deriv f n < m + δ with hP₂
  set p := A + ((Finset.Ioc A B).filter P₁).card with hp
  set q := A + ((Finset.Ioc A B).filter P₂).card with hq
  have hfilt₁ : (Finset.Ioc A B).filter P₁ = Finset.Ioc A p :=
    filter_eq_Ioc_of_downward A B P₁ fun n n' h1 h12 h2 hn' =>
      le_trans (hmonoN n n' h1 h12 h2) hn'
  have hfilt₂ : (Finset.Ioc A B).filter P₂ = Finset.Ioc A q :=
    filter_eq_Ioc_of_downward A B P₂ fun n n' h1 h12 h2 hn' =>
      lt_of_le_of_lt (hmonoN n n' h1 h12 h2) hn'
  have hpq : p ≤ q := by
    have : (Finset.Ioc A B).filter P₁ ⊆ (Finset.Ioc A B).filter P₂ :=
      Finset.monotone_filter_right _ fun n _ => by
        show deriv f n ≤ m - δ → deriv f n < m + δ
        intro hn
        linarith
    have := Finset.card_le_card this
    rw [hp, hq]
    omega
  have hqB : q ≤ B := by
    have := Finset.card_filter_le (Finset.Ioc A B) P₂
    rw [Nat.card_Ioc] at this
    rw [hq]
    omega
  have hAp : A ≤ p := by
    rw [hp]
    omega
  -- membership facts
  have hmem₁ : ∀ n, n ∈ Finset.Ioc A p ↔ n ∈ Finset.Ioc A B ∧ deriv f n ≤ m - δ := by
    intro n
    rw [← hfilt₁, Finset.mem_filter]
  have hmem₂ : ∀ n, n ∈ Finset.Ioc A q ↔ n ∈ Finset.Ioc A B ∧ deriv f n < m + δ := by
    intro n
    rw [← hfilt₂, Finset.mem_filter]
  rw [← Finset.sum_Ioc_consecutive _ (le_trans hAp hpq) hqB,
    ← Finset.sum_Ioc_consecutive _ hAp hpq]
  -- piece 1
  have hS₁ : ‖∑ n ∈ Finset.Ioc A p, e (f n)‖ ≤ 4 / δ := by
    rcases Nat.eq_or_lt_of_le hAp with h | h
    · rw [← h, Finset.Ioc_self, Finset.sum_empty, norm_zero]
      exact h4δ.le
    have hpB : p ≤ B := le_trans hpq hqB
    refine KL.kuzmin_landau f A p δ hδ hδ' hf1 (Or.inl (hmono.mono
      (Set.Icc_subset_Icc le_rfl (by exact_mod_cast hpB)))) fun t ht => ?_
    have hA1 : (A + 1 : ℕ) ∈ Finset.Ioc A B := by
      rw [Finset.mem_Ioc]
      omega
    have hpmem : p ∈ Finset.Ioc A p := by
      rw [Finset.mem_Ioc]
      omega
    have hlo : (m : ℝ) - 1 / 2 ≤ deriv f (A + 1 : ℕ) := (hwin _ hA1).1
    have hhi : deriv f p ≤ m - δ := ((hmem₁ p).1 hpmem).2
    have hsub : Set.Icc (A + 1 : ℝ) p ⊆ Set.Icc (A + 1 : ℝ) B :=
      Set.Icc_subset_Icc le_rfl (by exact_mod_cast hpB)
    have h1 : deriv f (A + 1 : ℕ) ≤ deriv f t := by
      apply hmono (hsub ⟨by push_cast; exact le_rfl, by push_cast; linarith [ht.1, ht.2]⟩) (hsub ht)
      push_cast
      exact ht.1
    have h2 : deriv f t ≤ deriv f p := by
      apply hmono (hsub ht) (hsub ⟨ht.1.trans ht.2, le_rfl⟩) ht.2
    push_cast at h1 hlo
    exact nearestIntDist_ge (m - 1) (by push_cast; linarith) (by push_cast; linarith)
  -- piece 3
  have hS₃ : ‖∑ n ∈ Finset.Ioc q B, e (f n)‖ ≤ 4 / δ := by
    rcases Nat.eq_or_lt_of_le hqB with h | h
    · rw [h, Finset.Ioc_self, Finset.sum_empty, norm_zero]
      exact h4δ.le
    have hAq : (A : ℝ) ≤ q := by exact_mod_cast le_trans hAp hpq
    refine KL.kuzmin_landau f q B δ hδ hδ' hf1 (Or.inl (hmono.mono
      (Set.Icc_subset_Icc (by push_cast; linarith) le_rfl))) fun t ht => ?_
    have hq1 : (q + 1 : ℕ) ∈ Finset.Ioc A B := by
      rw [Finset.mem_Ioc]
      omega
    have hq1' : (q + 1 : ℕ) ∉ Finset.Ioc A q := by
      rw [Finset.mem_Ioc]
      omega
    have hBmem : B ∈ Finset.Ioc A B := by
      rw [Finset.mem_Ioc]
      omega
    have hlo : (m : ℝ) + δ ≤ deriv f (q + 1 : ℕ) := by
      by_contra hcon
      push Not at hcon
      exact hq1' ((hmem₂ _).2 ⟨hq1, hcon⟩)
    have hhi : deriv f B < m + 1 / 2 := (hwin _ hBmem).2
    have hsub : Set.Icc (q + 1 : ℝ) B ⊆ Set.Icc (A + 1 : ℝ) B :=
      Set.Icc_subset_Icc (by push_cast; linarith) le_rfl
    have h1 : deriv f (q + 1 : ℕ) ≤ deriv f t := by
      apply hmono (hsub ⟨by push_cast; exact le_rfl, by push_cast; linarith [ht.1, ht.2]⟩) (hsub ht)
      push_cast
      exact ht.1
    have h2 : deriv f t ≤ deriv f B := by
      apply hmono (hsub ht) (hsub ⟨ht.1.trans ht.2, le_rfl⟩) ht.2
    push_cast at h1 hlo
    exact nearestIntDist_ge m (by linarith) (by linarith)
  -- piece 2: a trivial bound on the count
  have hS₂ : ‖∑ n ∈ Finset.Ioc p q, e (f n)‖ ≤ 2 / δ + 1 := by
    have hcount : ((q - p : ℕ) : ℝ) ≤ 2 / δ + 1 := by
      rcases Nat.lt_or_ge (p + 1) q with h | h
      · -- mean value theorem for `f'` on `[p+1, q]`
        have hlt : ((p + 1 : ℕ) : ℝ) < (q : ℕ) := by exact_mod_cast h
        obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope (deriv f) hlt
          hf'.continuous.continuousOn (hf'.differentiable one_ne_zero).differentiableOn
        have hcI : c ∈ Set.Icc (A + 1 : ℝ) B := by
          refine ⟨?_, ?_⟩
          · have : ((p + 1 : ℕ) : ℝ) ≥ A + 1 := by push_cast; linarith [(by exact_mod_cast hAp : (A : ℝ) ≤ p)]
            linarith [hc.1]
          · have : ((q : ℕ) : ℝ) ≤ B := by exact_mod_cast hqB
            linarith [hc.2]
        have hslope := h2 c hcI
        rw [hc'] at hslope
        have hqmem : q ∈ Finset.Ioc A q := by
          rw [Finset.mem_Ioc]
          omega
        have hp1 : (p + 1 : ℕ) ∉ Finset.Ioc A p := by
          rw [Finset.mem_Ioc]
          omega
        have hp1B : (p + 1 : ℕ) ∈ Finset.Ioc A B := by
          rw [Finset.mem_Ioc]
          omega
        have hq' : deriv f q < m + δ := ((hmem₂ q).1 hqmem).2
        have hp' : (m : ℝ) - δ < deriv f (p + 1 : ℕ) := by
          by_contra hcon
          push Not at hcon
          exact hp1 ((hmem₁ _).2 ⟨hp1B, hcon⟩)
        have hgap : 0 < ((q : ℕ) : ℝ) - ((p + 1 : ℕ) : ℝ) := by linarith
        rw [le_div_iff₀ hgap] at hslope
        have hdiff : deriv f q - deriv f (p + 1 : ℕ) < 2 * δ := by linarith
        have hqp : ((q - p : ℕ) : ℝ) = (q : ℝ) - p := by
          rw [Nat.cast_sub hpq]
        rw [hqp]
        push_cast at hslope hdiff
        have : δ ^ 2 * ((q : ℝ) - p - 1) < 2 * δ := by linarith
        have : (q : ℝ) - p - 1 < 2 / δ := by
          rw [lt_div_iff₀ hδ]
          nlinarith
        linarith
      · have : ((q - p : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (by omega : q - p ≤ 1)
        linarith
    calc ‖∑ n ∈ Finset.Ioc p q, e (f n)‖ ≤ ∑ n ∈ Finset.Ioc p q, ‖e (f n)‖ := norm_sum_le _ _
      _ = ((q - p : ℕ) : ℝ) := by simp [norm_e]
      _ ≤ 2 / δ + 1 := hcount
  calc ‖∑ n ∈ Finset.Ioc A p, e (f n) + ∑ n ∈ Finset.Ioc p q, e (f n) +
          ∑ n ∈ Finset.Ioc q B, e (f n)‖
      ≤ ‖∑ n ∈ Finset.Ioc A p, e (f n)‖ + ‖∑ n ∈ Finset.Ioc p q, e (f n)‖ +
          ‖∑ n ∈ Finset.Ioc q B, e (f n)‖ := norm_add₃_le
    _ ≤ 4 / δ + (2 / δ + 1) + 4 / δ := add_le_add (add_le_add hS₁ hS₂) hS₃
    _ = 10 / δ + 1 := by ring

/-- Bounds for `round`. -/
theorem round_bounds (x : ℝ) : (round x : ℝ) - 1 / 2 ≤ x ∧ x < round x + 1 / 2 := by
  have := round_eq_iff.1 (rfl : round x = round x)
  exact ⟨this.1, this.2⟩

theorem round_mono' {x y : ℝ} (h : x ≤ y) : round x ≤ round y := by
  rw [round_eq, round_eq]
  exact Int.floor_le_floor (by linarith)

theorem round_ge_of_ge {x : ℝ} {m : ℤ} (h : (m : ℝ) + 1 / 2 ≤ x) : m + 1 ≤ round x := by
  rw [round_eq, Int.le_floor]
  push_cast
  linarith

/-- Induction over windows: for `A < B`,
`‖∑_{A < n ≤ B} e(f(n))‖ ≤ (10/δ + 1) (round f'(B) - round f'(A+1) + 1)`. -/
theorem windows_bound (hf : ContDiff ℝ 2 f) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ∀ L A B : ℕ, B - A = L → A < B →
      MonotoneOn (deriv f) (Set.Icc (A + 1 : ℝ) B) →
      (∀ t ∈ Set.Icc (A + 1 : ℝ) B, δ ^ 2 ≤ deriv (deriv f) t) →
      ‖∑ n ∈ Finset.Ioc A B, e (f n)‖ ≤
        (10 / δ + 1) * ((round (deriv f B) : ℝ) - round (deriv f (A + 1 : ℕ)) + 1) := by
  classical
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
  intro A B hL hAB hmono h2
  have hW : 0 ≤ 10 / δ + 1 := by positivity
  have hmonoN : ∀ n n' : ℕ, A < n → n ≤ n' → n' ≤ B → deriv f n ≤ deriv f n' := by
    intro n n' h1 h12 h2
    apply hmono
    · exact ⟨by exact_mod_cast h1, by exact_mod_cast (le_trans h12 h2)⟩
    · exact ⟨by exact_mod_cast (lt_of_lt_of_le h1 h12), by exact_mod_cast h2⟩
    · exact_mod_cast h12
  set m : ℤ := round (deriv f (A + 1 : ℕ)) with hm
  set P : ℕ → Prop := fun n => deriv f n < m + 1 / 2 with hP
  set s := A + ((Finset.Ioc A B).filter P).card with hs
  have hfilt : (Finset.Ioc A B).filter P = Finset.Ioc A s :=
    filter_eq_Ioc_of_downward A B P fun n n' h1 h12 h2 hn' =>
      lt_of_le_of_lt (hmonoN n n' h1 h12 h2) hn'
  have hmem : ∀ n, n ∈ Finset.Ioc A s ↔ n ∈ Finset.Ioc A B ∧ deriv f n < m + 1 / 2 := by
    intro n
    rw [← hfilt, Finset.mem_filter]
  have hsB : s ≤ B := by
    have := Finset.card_filter_le (Finset.Ioc A B) P
    rw [Nat.card_Ioc] at this
    rw [hs]
    omega
  have hA1s : A + 1 ≤ s := by
    have : A + 1 ∈ Finset.Ioc A s := by
      rw [hmem]
      refine ⟨by rw [Finset.mem_Ioc]; omega, ?_⟩
      rw [hm]
      exact (round_bounds _).2
    rw [Finset.mem_Ioc] at this
    exact this.2
  -- the first window
  have hwin : ‖∑ n ∈ Finset.Ioc A s, e (f n)‖ ≤ 10 / δ + 1 := by
    have hsB' : (s : ℝ) ≤ B := by exact_mod_cast hsB
    refine window_bound f A s m δ hδ hδ' hf
      (hmono.mono (Set.Icc_subset_Icc le_rfl hsB'))
      (fun t ht => h2 t ⟨ht.1, ht.2.trans hsB'⟩) fun n hn => ?_
    have hn' := (hmem n).1 hn
    refine ⟨?_, hn'.2⟩
    have hA1 : deriv f (A + 1 : ℕ) ≤ deriv f n := by
      rw [Finset.mem_Ioc] at hn
      exact hmonoN (A + 1) n (by omega) hn.1 (le_trans hn.2 hsB)
    have := (round_bounds (deriv f (A + 1 : ℕ))).1
    rw [← hm] at this
    linarith
  have hmB : m ≤ round (deriv f B) := by
    rw [hm]
    exact round_mono' (hmonoN (A + 1) B (by omega) (by omega) le_rfl)
  have hmB' : (m : ℝ) ≤ round (deriv f B) := by exact_mod_cast hmB
  rcases Nat.eq_or_lt_of_le hsB with h | h
  · -- a single window
    rw [← h]
    calc ‖∑ n ∈ Finset.Ioc A s, e (f n)‖ ≤ 10 / δ + 1 := hwin
      _ = (10 / δ + 1) * 1 := by ring
      _ ≤ (10 / δ + 1) * ((round (deriv f s) : ℝ) - m + 1) := by
          apply mul_le_mul_of_nonneg_left _ hW
          rw [h]
          linarith
  · -- recurse on the remaining range
    have hnext : m + 1 ≤ round (deriv f (s + 1 : ℕ)) := by
      have hs1 : (s + 1 : ℕ) ∉ Finset.Ioc A s := by
        rw [Finset.mem_Ioc]
        omega
      have hs1B : (s + 1 : ℕ) ∈ Finset.Ioc A B := by
        rw [Finset.mem_Ioc]
        omega
      have : (m : ℝ) + 1 / 2 ≤ deriv f (s + 1 : ℕ) := by
        by_contra hcon
        push Not at hcon
        exact hs1 ((hmem _).2 ⟨hs1B, hcon⟩)
      exact round_ge_of_ge this
    have hnext' : (m : ℝ) + 1 ≤ round (deriv f (s + 1 : ℕ)) := by exact_mod_cast hnext
    have hsA : (A : ℝ) + 1 ≤ s := by exact_mod_cast hA1s
    have hrec := ih (B - s) (by omega) s B rfl h
      (hmono.mono (Set.Icc_subset_Icc (by linarith) le_rfl))
      (fun t ht => h2 t ⟨by linarith [ht.1], ht.2⟩)
    rw [← Finset.sum_Ioc_consecutive _ (by omega : A ≤ s) hsB]
    calc ‖∑ n ∈ Finset.Ioc A s, e (f n) + ∑ n ∈ Finset.Ioc s B, e (f n)‖
        ≤ ‖∑ n ∈ Finset.Ioc A s, e (f n)‖ + ‖∑ n ∈ Finset.Ioc s B, e (f n)‖ := norm_add_le _ _
      _ ≤ (10 / δ + 1) + (10 / δ + 1) *
            ((round (deriv f B) : ℝ) - round (deriv f (s + 1 : ℕ)) + 1) := add_le_add hwin hrec
      _ ≤ (10 / δ + 1) + (10 / δ + 1) * ((round (deriv f B) : ℝ) - (m + 1) + 1) := by
          gcongr
      _ = (10 / δ + 1) * ((round (deriv f B) : ℝ) - m + 1) := by ring

/-- **The van der Corput second-derivative test.**  If `f ∈ C²` and
`λ₂ ≤ f'' ≤ α λ₂` on `[A+1, B]` with `0 < λ₂ ≤ 1/4`, then
`‖∑_{A < n ≤ B} e(f(n))‖ ≤ 12 α (B - A) √λ₂ + 24 / √λ₂`. -/
theorem second_derivative (hf : ContDiff ℝ 2 f) (A B : ℕ) (lam2 α : ℝ)
    (hl : 0 < lam2) (hl' : lam2 ≤ 1 / 4) (hα : 0 ≤ α)
    (h2 : ∀ t ∈ Set.Icc (A + 1 : ℝ) B, lam2 ≤ deriv (deriv f) t ∧ deriv (deriv f) t ≤ α * lam2) :
    ‖∑ n ∈ Finset.Ioc A B, e (f n)‖ ≤
      12 * α * ((B - A : ℕ) : ℝ) * Real.sqrt lam2 + 24 / Real.sqrt lam2 := by
  set δ := Real.sqrt lam2 with hδdef
  have hδ : 0 < δ := Real.sqrt_pos.2 hl
  have hδ2 : δ ^ 2 = lam2 := Real.sq_sqrt hl.le
  have hδ' : δ ≤ 1 / 2 := by
    have h14 : Real.sqrt (1 / 4) = 1 / 2 := by
      rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hδdef, ← h14]
    exact Real.sqrt_le_sqrt hl'
  have h2δ : (1 : ℝ) ≤ 2 / δ := by
    rw [le_div_iff₀ hδ]
    linarith
  rcases Nat.lt_or_ge A B with hAB | hAB
  · have hf' : ContDiff ℝ 1 (deriv f) :=
      (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f from hf)).2.2
    have hmono : MonotoneOn (deriv f) (Set.Icc (A + 1 : ℝ) B) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hf'.continuous.continuousOn
        (hf'.differentiable one_ne_zero).differentiableOn fun x hx => ?_
      rw [interior_Icc] at hx
      exact le_trans hl.le (h2 x ⟨hx.1.le, hx.2.le⟩).1
    have hmain := windows_bound f hf δ hδ hδ' (B - A) A B rfl hAB hmono
      (fun t ht => by rw [hδ2]; exact (h2 t ht).1)
    have hA1 : (A + 1 : ℝ) ≤ B := by exact_mod_cast hAB
    have hdiff : deriv f B - deriv f (A + 1 : ℕ) ≤ α * lam2 * ((B - A : ℕ) : ℝ) := by
      rcases Nat.eq_or_lt_of_le (show A + 1 ≤ B from hAB) with h | h
      · rw [h]
        push_cast
        simp
        positivity
      · have hlt : ((A + 1 : ℕ) : ℝ) < (B : ℕ) := by exact_mod_cast h
        obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope (deriv f) hlt
          hf'.continuous.continuousOn (hf'.differentiable one_ne_zero).differentiableOn
        have hcI : c ∈ Set.Icc (A + 1 : ℝ) B := ⟨by push_cast at hc; linarith [hc.1], hc.2.le⟩
        have hle := (h2 c hcI).2
        rw [hc', div_le_iff₀ (by push_cast at hlt ⊢; linarith)] at hle
        have hBA : ((B - A : ℕ) : ℝ) = (B : ℝ) - A := by rw [Nat.cast_sub hAB.le]
        rw [hBA]
        push_cast at hle ⊢
        nlinarith [mul_nonneg hα hl.le]
    have hr1 := round_bounds (deriv f B)
    have hr2 := round_bounds (deriv f (A + 1 : ℕ))
    have hcount : (round (deriv f B) : ℝ) - round (deriv f (A + 1 : ℕ)) + 1 ≤
        α * lam2 * ((B - A : ℕ) : ℝ) + 2 := by linarith
    have hW : 10 / δ + 1 ≤ 12 / δ := by
      have : 12 / δ = 10 / δ + 2 / δ := by ring
      linarith
    have hcount0 : 0 ≤ α * lam2 * ((B - A : ℕ) : ℝ) + 2 := by positivity
    have hmono1 : deriv f (A + 1 : ℕ) ≤ deriv f B :=
      hmono ⟨by push_cast; exact le_rfl, by push_cast; exact hA1⟩ ⟨hA1, le_rfl⟩ (by push_cast; exact hA1)
    have hrnn : 0 ≤ (round (deriv f B) : ℝ) - round (deriv f (A + 1 : ℕ)) + 1 := by
      have := round_mono' hmono1
      have : (round (deriv f (A + 1 : ℕ)) : ℝ) ≤ round (deriv f B) := by exact_mod_cast this
      linarith
    calc ‖∑ n ∈ Finset.Ioc A B, e (f n)‖
        ≤ (10 / δ + 1) * ((round (deriv f B) : ℝ) - round (deriv f (A + 1 : ℕ)) + 1) := hmain
      _ ≤ (12 / δ) * (α * lam2 * ((B - A : ℕ) : ℝ) + 2) := mul_le_mul hW hcount hrnn (by positivity)
      _ = 12 * α * ((B - A : ℕ) : ℝ) * δ + 24 / δ := by
          rw [← hδ2]
          field_simp
          ring
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
    positivity


end VdC

end LeanProofs.IntegerPoints
