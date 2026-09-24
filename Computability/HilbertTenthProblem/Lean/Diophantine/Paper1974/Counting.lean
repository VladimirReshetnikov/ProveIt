import Diophantine.Paper1974.More

/-!
# Jones 1974: counting halting machines, and shifts against scanned squares

* `L_n = 4(4n+4)^(2n-1) ≤ H(n)`: the machines whose first card `(1, 0)` halts already
  halt after one step (the editorial proof detail after the paper's (2));
* for `n ≥ 1`, `H(n) < (4n+4)^(2n) < L_(n+1) ≤ H(n+1)`, so `H` is strictly increasing,
  and the intervals `[L_n, U_n)` determine `n` from `H(n)`;
* the paper's (4): `SH(n) ≤ n · SC(n) · 2^SC(n)`, by counting the configurations
  (active state, scanned square, contents of the scanned squares) of a halting run,
  none of which can repeat;
* the first row of the paper's table: `Σ(1) = SC(1) = SH(1) = 1` and `H(1) = 32`.
-/

namespace Jones1974

open Classical

variable {n : ℕ}

/-! ### `L_n ≤ H(n)` -/

/-- A machine whose first card on a blank square halts, halts after one step. -/
theorem halts_of_first_card {M : Machine n} (hn : 0 < n)
    (h : (M.card ⟨0, hn⟩ false).next = none) : Halts M :=
  ⟨1, by simp [run_succ, step, init, startState, hn, blank, h]⟩

/-- The halting actions: overprint and shift are free, the next state is `0`. -/
def haltAction (n : ℕ) : {a : Action n // a.next = none} ≃ Bool × Move where
  toFun a := (a.1.write, a.1.move)
  invFun p := ⟨⟨p.1, p.2, none⟩, rfl⟩
  left_inv a := by
    obtain ⟨⟨w, m, nx⟩, h⟩ := a
    simp only at h
    subst h
    rfl
  right_inv _ := rfl

/-- The machines whose first card on a blank square halts. -/
def firstHalt (n : ℕ) (hn : 0 < n) :
    {M : Machine n // (M.card ⟨0, hn⟩ false).next = none} ≃
      {a : Action n // a.next = none} × ({j : Fin n × Bool // j ≠ (⟨0, hn⟩, false)} → Action n) :=
  (Equiv.subtypeEquiv ((Machine.equiv n).trans ((Equiv.curry _ _ _).symm.trans
      (Equiv.funSplitAt ((⟨0, hn⟩ : Fin n), false) (Action n))))
    (q := fun s => s.1.next = none) (fun _ => Iff.rfl)).trans
    (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun a : Action n => a.next = none))

theorem card_firstHalt (n : ℕ) (hn : 0 < n) :
    Fintype.card {M : Machine n // (M.card ⟨0, hn⟩ false).next = none} =
      4 * (4 * n + 4) ^ (2 * n - 1) := by
  rw [Fintype.card_congr (firstHalt n hn), Fintype.card_prod, Fintype.card_congr (haltAction n),
    Fintype.card_prod, Fintype.card_bool, card_move, Fintype.card_fun, card_action,
    Fintype.card_subtype_compl, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    Fintype.card_unique]
  ring_nf

/-- `L_n ≤ H(n)`. -/
theorem L_le_H (hn : 0 < n) : 4 * (4 * n + 4) ^ (2 * n - 1) ≤ H n := by
  rw [← card_firstHalt n hn, H, Fintype.card_subtype]
  exact Finset.card_le_card (fun M hM => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM ⊢
    exact halts_of_first_card hn hM)

/-- `H(0) = 1`: the only `0`-state machine halts at once. -/
theorem H_zero : H 0 = 1 := by
  rw [H, Finset.filter_true_of_mem (fun M _ => ⟨0, by simp [init, startState]⟩), Finset.card_univ,
    card_machine]
  norm_num

/-- `U_n < L_(n+1)`. -/
theorem U_lt_L (n : ℕ) : (4 * n + 4) ^ (2 * n) < 4 * (4 * (n + 1) + 4) ^ (2 * (n + 1) - 1) := by
  have h1 : (4 * n + 4) ^ (2 * n) ≤ (4 * (n + 1) + 4) ^ (2 * n) :=
    Nat.pow_le_pow_left (by omega) _
  have h2 : (4 * (n + 1) + 4) ^ (2 * n) ≤ (4 * (n + 1) + 4) ^ (2 * (n + 1) - 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : 0 < (4 * (n + 1) + 4) ^ (2 * (n + 1) - 1) := by positivity
  omega

/-- `H` is strictly increasing. -/
theorem H_strictMono : StrictMono H := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · change H 0 < H 1
    rw [H_zero]
    have := L_le_H (n := 1) (by norm_num)
    norm_num at this
    omega
  · exact (H_lt k hk).trans_le ((U_lt_L k).le.trans (L_le_H (by omega)))

/-- `H(n)` lies in `[L_n, U_n)`, and these intervals are disjoint for different `n ≥ 1`;
so `n` is determined by the value `H(n)`. -/
theorem H_mem_interval (hn : 0 < n) :
    4 * (4 * n + 4) ^ (2 * n - 1) ≤ H n ∧ H n < (4 * n + 4) ^ (2 * n) :=
  ⟨L_le_H hn, H_lt n hn⟩

/-! ### The paper's (4) -/

theorem scanned_mono (M : Machine n) {s t : ℕ} (h : s ≤ t) : scanned M s ⊆ scanned M t :=
  fun _ ⟨r, hr, h1, h2⟩ => ⟨r, by omega, h1, h2⟩

/-- A halting run never repeats a configuration before halting. -/
theorem run_injective_before_halt {M : Machine n} {T s s' : ℕ} (hT : HaltsInExactly M T)
    (hs : s < s') (hs' : s' < T) : run M (init n) s ≠ run M (init n) s' := by
  intro heq
  have h1 : run M (init n) T = run M (init n) (s + (T - s')) := by
    rw [run_add, heq, ← run_add]; congr 1; omega
  exact hT.2 (s + (T - s')) (by omega) (h1 ▸ hT.1)

/-- The halting time is at most `n · |S| · 2^|S|` for the set `S` of scanned squares. -/
theorem haltTime_le_scanCount {M : Machine n} (hM : Halts M) :
    haltTime M ≤ n * scanCount M * 2 ^ scanCount M := by
  set T := haltTime M with hTdef
  have hT := haltsInExactly_haltTime hM
  rw [← hTdef] at hT
  set S := (scanned_finite M T).toFinset with hS
  have hcard : scanCount M = S.card := by
    rw [scanCount, ← hTdef, hS, Set.ncard_eq_toFinset_card _ (scanned_finite M T)]
  have hactive : ∀ s : Fin T, (run M (init n) s).state ≠ none := fun s => hT.2 s s.isLt
  let f : Fin T → Fin n × S × (S → Bool) := fun s =>
    ((run M (init n) s).state.get (Option.isSome_iff_ne_none.2 (hactive s)),
      ⟨(run M (init n) s).head, by
        rw [hS, Set.Finite.mem_toFinset]; exact ⟨s, s.isLt, hactive s, rfl⟩⟩,
      fun p => (run M (init n) s).tape p)
  have hinj : Function.Injective f := by
    intro s s' hss
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at hss
    obtain ⟨hq, hh, htape⟩ := hss
    have hconf : run M (init n) s = run M (init n) s' := by
      have hq' : (run M (init n) s).state = (run M (init n) s').state := by
        rw [← Option.some_get (Option.isSome_iff_ne_none.2 (hactive s)),
          ← Option.some_get (Option.isSome_iff_ne_none.2 (hactive s')), hq]
      have ht : (run M (init n) s).tape = (run M (init n) s').tape := by
        funext p
        by_cases hp : p ∈ S
        · exact congrFun htape ⟨p, hp⟩
        · have hout : ∀ r : Fin T, (run M (init n) r).tape p = false := by
            intro r
            by_contra hne
            have hmem : p ∈ scanned M T :=
              scanned_mono M r.isLt.le (ones_subset_scanned M r (by simpa [ones] using hne))
            exact hp (by rw [hS, Set.Finite.mem_toFinset]; exact hmem)
          rw [hout s, hout s']
      cases h1 : run M (init n) s
      cases h2 : run M (init n) s'
      rw [h1, h2] at hq' ht
      rw [h1, h2] at hh
      simp only at hq' ht hh
      rw [hq', ht, hh]
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact run_injective_before_halt hT hlt s'.isLt hconf
    · exact run_injective_before_halt hT hlt s.isLt hconf.symm
  have := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_coe] at this
  rw [hcard]
  calc T ≤ n * (S.card * 2 ^ S.card) := this
    _ = n * S.card * 2 ^ S.card := by ring

/-- **The paper's (4)**: `SH(n) ≤ n · SC(n) · 2^SC(n)`. -/
theorem SH_le (n : ℕ) : SH n ≤ n * SC n * 2 ^ SC n := by
  rw [SH]
  apply Finset.sup_le
  intro M hM
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
  calc haltTime M ≤ n * scanCount M * 2 ^ scanCount M := haltTime_le_scanCount hM
    _ ≤ n * SC n * 2 ^ SC n :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (le_SC hM)) (Nat.pow_le_pow_right (by norm_num) (le_SC hM))

/-! ### The first row of the table -/

/-- A `1`-state machine whose first card does not halt keeps reading blank squares. -/
theorem not_halts_one {M : Machine 1} (h : (M.card 0 false).next = some 0) : ¬ Halts M := by
  set a := M.card 0 false with ha
  have hinv : ∀ t, (run M (init 1) t).state = some 0 ∧
      ∀ p, (a.move = .R ∧ (run M (init 1) t).head ≤ p ∨ a.move = .L ∧ p ≤ (run M (init 1) t).head) →
        (run M (init 1) t).tape p = false := by
    intro t
    induction t with
    | zero =>
      refine ⟨by simp [init, startState], fun p _ => rfl⟩
    | succ t ih =>
      obtain ⟨hs, hb⟩ := ih
      have hread : (run M (init 1) t).tape (run M (init 1) t).head = false :=
        hb _ (by cases hm : a.move <;> simp)
      have hq : (0 : Fin 1) = ⟨0, by norm_num⟩ := rfl
      rw [run_succ]
      simp only [step, hs, hread, ← ha]
      refine ⟨h, fun p hp => ?_⟩
      have hne : p ≠ (run M (init 1) t).head := by
        rcases hp with ⟨hm, hp⟩ | ⟨hm, hp⟩ <;> simp only [hm, Move.apply] at hp <;> omega
      rw [Function.update_of_ne hne]
      apply hb
      rcases hp with ⟨hm, hp⟩ | ⟨hm, hp⟩ <;> simp only [hm, Move.apply] at hp
      · exact Or.inl ⟨hm, by omega⟩
      · exact Or.inr ⟨hm, by omega⟩
  rintro ⟨t, ht⟩
  rw [(hinv t).1] at ht
  exact Option.some_ne_none _ ht

theorem halts_one_iff {M : Machine 1} : Halts M ↔ (M.card 0 false).next = none := by
  constructor
  · intro hM
    cases hc : (M.card 0 false).next with
    | none => rfl
    | some q =>
      have : q = 0 := Subsingleton.elim _ _
      subst this
      exact absurd hM (not_halts_one hc)
  · exact halts_of_first_card (n := 1) (by norm_num)

/-- `H(1) = 32`. -/
theorem H_one : H 1 = 32 := by
  have h := card_firstHalt 1 (by norm_num)
  rw [Fintype.card_subtype] at h
  rw [H, Finset.filter_congr (fun M _ => halts_one_iff)]
  exact h

/-- A halting `1`-state machine halts after exactly one shift. -/
theorem haltsInExactly_one {M : Machine 1} (hM : Halts M) : HaltsInExactly M 1 := by
  refine ⟨?_, fun s hs => ?_⟩
  · simp [run_succ, step, init, startState, blank, halts_one_iff.1 hM]
  · obtain rfl : s = 0 := by omega
    simp [init, startState]

set_option linter.constructorNameAsVariable false in
theorem SH_one_le : SH 1 ≤ 1 := by
  rw [SH]
  apply Finset.sup_le
  intro M hM
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
  rw [haltTime_eq (haltsInExactly_one hM)]

/-- The machine printing one `1` and halting. -/
def printOne : Machine 1 where
  card _ _ := ⟨true, .R, none⟩

theorem one_le_sigma_one : 1 ≤ sigma 1 := by
  apply le_sigma (M := printOne)
  refine ⟨1, by simp [run_succ, step, init, startState, printOne], ?_⟩
  have : ones (run printOne (init 1) 1) = {0} := by
    ext p
    by_cases hp : p = 0
    · subst hp; simp [ones, run_succ, step, init, startState, printOne]
    · simp [ones, run_succ, step, init, startState, printOne, blank, hp]
  rw [this, Set.ncard_singleton]

/-- **The table, `n = 1`**: `Σ(1) = SC(1) = SH(1) = 1` and `H(1) = 32`. -/
theorem table_one : sigma 1 = 1 ∧ SC 1 = 1 ∧ SH 1 = 1 ∧ H 1 = 32 := by
  have h1 := one_le_sigma_one
  have h2 := sigma_le_SC 1
  have h3 := SC_le_SH 1
  have h4 := SH_one_le
  exact ⟨by omega, by omega, by omega, H_one⟩

end Jones1974
