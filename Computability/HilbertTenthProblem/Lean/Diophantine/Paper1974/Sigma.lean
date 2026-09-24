import Diophantine.Paper1974.Doubler
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Jones 1974: Radó's function `Σ` and the theorems

* `sigma n` = `Σ(n)`: the largest score of a halting `n`-state machine (well defined
  since there are finitely many machines);
* `sigma_mono`: `Σ(n) ≤ Σ(n+1)` (padding with an unreachable state); the strict inequality
  `Σ(n) < Σ(n+1)` that the paper remarks on is `sigma_lt_succ` in `More.lean` (a new state
  that scans right across ones and overprints the first zero);
* **Theorem 1**: for an increasing Turing computable `f`, `f(n) < Σ(n)` for all
  `n ≥ 12 + 2c`, where `c` is the number of states of a machine computing `f`
  (the composite `M[T[M^(x)]]` has `x + 6 + c` states and prints `f(2x) + 1` ones);
* **Corollary 1**: the same for every Turing computable `f`.  The paper reduces to
  Theorem 1 through `f̂(n) = n + Σ_{i≤n} f(i)`, whose Turing computability it takes
  from Kleene; here the odd values are reached directly with the 3-state successor
  machine, so no closure property of computability is needed;
* `Σ` is not Turing computable;
* `SH(n)`, the maximum number of shifts of a halting `n`-state machine, `Σ(n) ≤ SH(n)`,
  and **Theorem 2**: in the Turing machine game neither player has a computable
  winning strategy.
-/

namespace Jones1974

open Classical

variable {n : ℕ}

/-! ### The score function and `Σ` -/

/-- The score of a machine (`0` if it never halts). -/
noncomputable def score (M : Machine n) : ℕ :=
  if h : ∃ s, HaltsWithScore M s then Classical.choose h else 0

theorem score_spec {M : Machine n} {s : ℕ} (h : HaltsWithScore M s) : score M = s := by
  unfold score
  rw [dif_pos ⟨s, h⟩]
  exact score_unique (Classical.choose_spec (⟨s, h⟩ : ∃ s, HaltsWithScore M s)) h

/-- Radó's `Σ(n)`. -/
noncomputable def sigma (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun M : Machine n => Halts M)).sup score

theorem halts_of_haltsWithScore {M : Machine n} {s : ℕ} (h : HaltsWithScore M s) : Halts M :=
  let ⟨t, ht, _⟩ := h; ⟨t, ht⟩

theorem le_sigma {M : Machine n} {s : ℕ} (h : HaltsWithScore M s) : s ≤ sigma n := by
  rw [← score_spec h]
  apply Finset.le_sup (f := score)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact halts_of_haltsWithScore h

/-- `Σ(n)` is attained by some halting machine (for `n ≥ 1`; for `n = 0` it is `0`). -/
theorem exists_sigma_witness (hn : 0 < n) : ∃ M : Machine n, HaltsWithScore M (sigma n) := by
  -- the filtered set is nonempty: the machine that halts at once
  have hne : (Finset.univ.filter (fun M : Machine n => Halts M)).Nonempty := by
    refine ⟨⟨fun _ _ => ⟨false, .R, none⟩⟩, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨1, ?_⟩
    simp [run_succ, step, init, startState, dif_pos hn]
  obtain ⟨M, hM, hsup⟩ := Finset.exists_mem_eq_sup _ hne score
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
  obtain ⟨t, ht⟩ := hM
  refine ⟨M, t, ht, ?_⟩
  have : HaltsWithScore M (ones (run M (init n) t)).ncard := ⟨t, ht, rfl⟩
  rw [sigma, hsup, score_spec this]

/-! ### Monotonicity of `Σ` -/

/-- Padding a machine with one extra (unreachable) state. -/
def pad (M : Machine n) : Machine (n + 1) where
  card q b :=
    if h : q.val < n then
      let a := M.card ⟨q.val, h⟩ b
      ⟨a.write, a.move, a.next.map Fin.castSucc⟩
    else ⟨false, .R, none⟩

/-- Embedding configurations. -/
def Config.castSucc (c : Config n) : Config (n + 1) := ⟨c.state.map Fin.castSucc, c.head, c.tape⟩

theorem step_pad (M : Machine n) (c : Config n) : step (pad M) c.castSucc = (step M c).castSucc := by
  cases hs : c.state with
  | none => simp [step, Config.castSucc, hs]
  | some q =>
    have hq : q.val < n := q.isLt
    simp only [step, Config.castSucc, hs, Option.map_some, pad, Fin.val_castSucc, dif_pos hq, Fin.eta]

theorem run_pad (M : Machine n) (c : Config n) (t : ℕ) :
    run (pad M) c.castSucc t = (run M c t).castSucc := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, ih, step_pad, run_succ]

theorem init_castSucc (hn : 0 < n) : (init n).castSucc = init (n + 1) := by
  simp [init, Config.castSucc, startState, dif_pos hn]

theorem haltsWithScore_pad {M : Machine n} {s : ℕ} (hn : 0 < n) (h : HaltsWithScore M s) :
    HaltsWithScore (pad M) s := by
  obtain ⟨t, ht, hs⟩ := h
  refine ⟨t, ?_, ?_⟩
  · rw [← init_castSucc hn, run_pad]
    simp [Config.castSucc, ht]
  · rw [← init_castSucc hn, run_pad]
    exact hs

theorem sigma_mono (n : ℕ) : sigma n ≤ sigma (n + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- Σ(0): the only machine has no states; its score is 0
    rw [sigma]
    apply Finset.sup_le
    intro M hM
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
    obtain ⟨t, ht⟩ := hM
    have hz : HaltsWithScore M 0 := by
      refine ⟨0, ?_, ?_⟩
      · simp [init, startState]
      · simp [init, ones, blank]
    rw [score_spec hz]
    exact Nat.zero_le _
  · obtain ⟨M, hM⟩ := exists_sigma_witness hn
    exact le_sigma (haltsWithScore_pad hn hM)

theorem sigma_monotone : Monotone sigma := monotone_nat_of_le_succ sigma_mono

/-! ### Theorem 1 -/

/-- The composite `M[T[M^(x)]]` prints `f(2x) + 1` ones with `x + 6 + c` states. -/
theorem composite_even {c : ℕ} {M : Machine c} {f : ℕ → ℕ} (hM : Computes M f) {x : ℕ}
    (hx : 1 ≤ x) : f (2 * x) + 1 ≤ sigma (x + 1 + 5 + c) := by
  have h1 : PrintsFromBlank (seq (printer x) doubler) (2 * x) :=
    prints_seq (printer_prints hx) doubler_computes
  have h2 : PrintsFromBlank (seq (seq (printer x) doubler) M) (f (2 * x)) := prints_seq h1 hM
  exact le_sigma (haltsWithScore_of_prints h2)

/-- The composite `M[S[T[M^(x)]]]` (with the successor machine `S`) prints `f(2x+1) + 1` ones
with `x + 9 + c` states. -/
theorem composite_odd {c : ℕ} {M : Machine c} {f : ℕ → ℕ} (hM : Computes M f) {x : ℕ}
    (hx : 1 ≤ x) : f (2 * x + 1) + 1 ≤ sigma (x + 1 + 5 + 3 + c) := by
  have h1 : PrintsFromBlank (seq (printer x) doubler) (2 * x) :=
    prints_seq (printer_prints hx) doubler_computes
  have h2 : PrintsFromBlank (seq (seq (printer x) doubler) succ1) (2 * x + 1) :=
    prints_seq (y := 2 * x) h1 succ1_computes
  have h3 : PrintsFromBlank (seq (seq (seq (printer x) doubler) succ1) M) (f (2 * x + 1)) :=
    prints_seq h2 hM
  exact le_sigma (haltsWithScore_of_prints h3)

/-- **Theorem 1** (with the paper's bound). Let `f` be increasing and computed by a machine
with `c` states. Then `f(n) < Σ(n)` for all `n ≥ 12 + 2c`. -/
theorem theorem_1 {c : ℕ} {M : Machine c} {f : ℕ → ℕ} (hM : Computes M f) (hf : Monotone f) :
    ∀ n, 12 + 2 * c ≤ n → f n < sigma n := by
  intro n hn
  obtain ⟨x, hx⟩ : ∃ x, n = x + 6 + c := ⟨n - 6 - c, by omega⟩
  have hx1 : 1 ≤ x := by omega
  have h := composite_even hM hx1
  have hmono : f n ≤ f (2 * x) := hf (by omega)
  have : x + 1 + 5 + c = n := by omega
  rw [this] at h
  omega

/-- **Corollary 1.** For every Turing computable `f`, `f(n) < Σ(n)` for all large `n`. -/
theorem corollary_1 {f : ℕ → ℕ} (hf : TMComputable f) : ∃ N, ∀ n, N ≤ n → f n < sigma n := by
  obtain ⟨c, M, hM⟩ := hf
  refine ⟨17 + 2 * c, fun n hn => ?_⟩
  rcases Nat.even_or_odd n with ⟨x, hx⟩ | ⟨x, hx⟩
  · -- n = 2x
    have hx1 : 1 ≤ x := by omega
    have h := composite_even hM hx1
    have hle : sigma (x + 1 + 5 + c) ≤ sigma n := sigma_monotone (by omega)
    have : 2 * x = n := by omega
    rw [this] at h
    omega
  · -- n = 2x + 1
    have hx1 : 1 ≤ x := by omega
    have h := composite_odd hM hx1
    have hle : sigma (x + 1 + 5 + 3 + c) ≤ sigma n := sigma_monotone (by omega)
    rw [← hx] at h
    omega

/-- **`Σ` is not Turing computable** (in particular, it has no computable upper bound). -/
theorem sigma_not_computable : ¬ TMComputable sigma := by
  intro h
  obtain ⟨N, hN⟩ := corollary_1 h
  exact lt_irrefl _ (hN N le_rfl)

/-- No Turing computable function bounds `Σ` from above. -/
theorem no_computable_bound {f : ℕ → ℕ} (hf : TMComputable f) : ¬ ∀ n, sigma n ≤ f n := by
  intro hb
  obtain ⟨N, hN⟩ := corollary_1 hf
  exact absurd (hb N) (not_le.2 (hN N le_rfl))

/-! ### Shifts: `SH` and the Turing machine game -/

/-- `M` halts after exactly `t` shifts (from the blank tape). -/
def HaltsInExactly (M : Machine n) (t : ℕ) : Prop :=
  (run M (init n) t).state = none ∧ ∀ s < t, (run M (init n) s).state ≠ none

/-- The halting time of a machine (`0` if it never halts). -/
noncomputable def haltTime (M : Machine n) : ℕ :=
  if h : Halts M then Nat.find h else 0

theorem haltsInExactly_haltTime {M : Machine n} (h : Halts M) : HaltsInExactly M (haltTime M) := by
  unfold haltTime
  rw [dif_pos h]
  exact ⟨Nat.find_spec h, fun s hs => Nat.find_min h hs⟩

theorem haltTime_eq {M : Machine n} {t : ℕ} (h : HaltsInExactly M t) : haltTime M = t := by
  have hh : Halts M := ⟨t, h.1⟩
  unfold haltTime
  rw [dif_pos hh]
  apply le_antisymm
  · exact Nat.find_min' hh h.1
  · by_contra hlt
    push_neg at hlt
    exact h.2 _ hlt (Nat.find_spec hh)

/-- `SH(n)`: the maximum number of shifts of a halting `n`-state machine. -/
noncomputable def SH (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun M : Machine n => Halts M)).sup haltTime

theorem le_SH {M : Machine n} {t : ℕ} (h : HaltsInExactly M t) : t ≤ SH n := by
  rw [← haltTime_eq h]
  apply Finset.le_sup (f := haltTime)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨t, h.1⟩

/-- Each step prints at most one new one. -/
theorem ncard_ones_run_le (M : Machine n) (t : ℕ) : (ones (run M (init n) t)).ncard ≤ t := by
  induction t with
  | zero =>
    have : ones (run M (init n) 0) = ∅ := by
      ext p; simp [ones, init, blank]
    rw [this, Set.ncard_empty]
  | succ t ih =>
    have hfin := ones_finite M t
    have hsub : ones (run M (init n) (t + 1)) ⊆ insert (run M (init n) t).head (ones (run M (init n) t)) := by
      intro p hp
      rw [run_succ] at hp
      simp only [ones, Set.mem_setOf_eq, step] at hp
      cases hs : (run M (init n) t).state with
      | none => rw [hs] at hp; exact Set.mem_insert_of_mem _ hp
      | some q =>
        rw [hs] at hp
        simp only at hp
        by_cases hpq : p = (run M (init n) t).head
        · rw [hpq]; exact Set.mem_insert _ _
        · rw [Function.update_of_ne hpq] at hp
          exact Set.mem_insert_of_mem _ hp
    calc (ones (run M (init n) (t + 1))).ncard
        ≤ (insert (run M (init n) t).head (ones (run M (init n) t))).ncard :=
          Set.ncard_le_ncard hsub (hfin.insert _)
      _ ≤ (ones (run M (init n) t)).ncard + 1 := Set.ncard_insert_le _ _
      _ ≤ t + 1 := by omega

/-- `Σ(n) ≤ SH(n)`. -/
theorem sigma_le_SH (n : ℕ) : sigma n ≤ SH n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : sigma 0 ≤ sigma 1 := sigma_mono 0
    -- Σ(0) = 0: the only 0-state machine halts at once with score 0
    rw [sigma]
    apply Finset.sup_le
    intro M hM
    have hz : HaltsWithScore M 0 := ⟨0, by simp [init, startState], by simp [init, ones, blank]⟩
    rw [score_spec hz]
    exact Nat.zero_le _
  · obtain ⟨M, t, ht, hs⟩ := exists_sigma_witness hn
    obtain ⟨t', ht', hmin⟩ := exists_first_halt ⟨t, ht⟩
    rw [run_eq_of_halted ht ht'] at hs
    calc sigma n = (ones (run M (init n) t')).ncard := hs.symm
      _ ≤ t' := ncard_ones_run_le M t'
      _ ≤ SH n := le_SH ⟨ht', hmin⟩

/-- A strategy for player II is a function `m = f(n)`; it is winning iff no `n`-state machine
halts in exactly `m + k` shifts for any positive `k`. -/
def WinningII (f : ℕ → ℕ) : Prop :=
  ∀ n k, 1 ≤ k → ¬ ∃ M : Machine n, HaltsInExactly M (f n + k)

theorem winningII_iff (f : ℕ → ℕ) : WinningII f ↔ ∀ n, SH n ≤ f n := by
  constructor
  · intro hw n
    by_contra hlt
    push_neg at hlt
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- SH 0 = 0
      have : SH 0 ≤ 0 := by
        rw [SH]; apply Finset.sup_le
        intro M _
        have : HaltsInExactly M 0 := ⟨by simp [init, startState], fun s hs => by omega⟩
        rw [haltTime_eq this]
      omega
    · -- a machine attaining SH n
      have hne : (Finset.univ.filter (fun M : Machine n => Halts M)).Nonempty := by
        refine ⟨⟨fun _ _ => ⟨false, .R, none⟩⟩, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨1, by simp [run_succ, step, init, startState, dif_pos hn]⟩
      obtain ⟨M, hM, hsup⟩ := Finset.exists_mem_eq_sup _ hne haltTime
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
      have hex := haltsInExactly_haltTime hM
      rw [SH, hsup] at hlt
      exact hw n (haltTime M - f n) (by omega) ⟨M, by rwa [show f n + (haltTime M - f n) = haltTime M by omega]⟩
  · intro hb n k hk ⟨M, hM⟩
    have := le_SH hM
    have := hb n
    omega

/-- Player II has a winning strategy, namely `SH`. -/
theorem SH_winning : WinningII SH := (winningII_iff SH).2 (fun _ => le_rfl)

/-- **Theorem 2** (player II). No Turing computable strategy is winning for player II. -/
theorem no_computable_winningII {f : ℕ → ℕ} (hf : TMComputable f) : ¬ WinningII f := by
  intro hw
  rw [winningII_iff] at hw
  apply no_computable_bound hf
  intro n
  exact (sigma_le_SH n).trans (hw n)

/-- A strategy for player I: a first move `n` and a reply `k = g(m)` to `m` (positive integers).
It is winning iff for every `m ≥ 1`, some `n`-state machine halts in exactly `m + g m` shifts. -/
def WinningI (n : ℕ) (g : ℕ → ℕ) : Prop :=
  ∀ m, 1 ≤ m → ∃ M : Machine n, HaltsInExactly M (m + g m)

/-- **Theorem 2** (player I). Player I has no winning strategy at all. -/
theorem no_winningI (n : ℕ) (g : ℕ → ℕ) (hg : ∀ m, 1 ≤ g m) : ¬ WinningI n g := by
  intro hw
  obtain ⟨M, hM⟩ := hw (SH n + 1) (by omega)
  have := le_SH hM
  have := hg (SH n + 1)
  omega

end Jones1974
