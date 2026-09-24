import Diophantine.Paper1974.Sigma

/-!
# Jones 1974: `Σ(n) < Σ(n+1)`, the functions `SC` and `H`

* The paper's remark after the definition of `Σ`: "with an additional card, a machine
  may be instructed to move right across ones to overprint with 1 the first 0
  encountered, and halt", so `Σ(n) < Σ(n+1)`.  We implement the extra card as the
  1-state machine `addOne` appended by `seq`.
* `SC(n)`: the maximum number of squares scanned in an active state by a halting
  `n`-state machine; `Σ(n) ≤ SC(n) ≤ SH(n)`, hence `SC` is not Turing computable.
* `H(n)`: the number of halting `n`-state machines; `H(n) < (4n+4)^(2n)` (the paper's
  (2)).  Its non-computability is argued in the paper by dovetailing and is not
  formalized.
-/

namespace Jones1974

open Classical

variable {n : ℕ}

/-! ### `Σ(n) < Σ(n+1)` -/

/-- The extra card: on a one move right (staying), on a zero overprint a one, move right, halt. -/
def addOne : Machine 1 where
  card _ b := if b then ⟨true, .R, some ⟨0, by norm_num⟩⟩ else ⟨true, .R, none⟩

theorem addOne_true : addOne.card ⟨0, by norm_num⟩ true = ⟨true, .R, some ⟨0, by norm_num⟩⟩ := rfl
theorem addOne_false : addOne.card ⟨0, by norm_num⟩ false = ⟨true, .R, none⟩ := rfl

/-- Started on a tape with finitely many ones, `addOne` halts with one more one. -/
theorem addOne_adds (tape : ℤ → Bool) (h : ℤ) (hfin : {p | tape p = true}.Finite) :
    ∃ t, (run addOne ⟨some ⟨0, by norm_num⟩, h, tape⟩ t).state = none ∧
      {p | (run addOne ⟨some ⟨0, by norm_num⟩, h, tape⟩ t).tape p = true}.ncard
        = {p | tape p = true}.ncard + 1 := by
  -- some position ≥ h carries a zero
  have hex : ∃ k : ℕ, tape (h + k) = false := by
    by_contra hcon
    push Not at hcon
    have : Set.Infinite {p | tape p = true} := by
      apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => h + k)
      · intro a b hab; simp at hab; exact hab
      · intro k; simp only [Set.mem_setOf_eq]
        cases hk : tape (h + k) with
        | false => exact absurd hk (hcon k)
        | true => rfl
    exact this hfin
  obtain ⟨k, hk, hmin⟩ : ∃ k : ℕ, tape (h + k) = false ∧ ∀ j < k, tape (h + j) ≠ false :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hsweep : run addOne ⟨some ⟨0, by norm_num⟩, h, tape⟩ k = ⟨some ⟨0, by norm_num⟩, h + k, tape⟩ := by
    apply sweep_right addOne_true
    intro p hp1 hp2
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, p = h + j := ⟨(p - h).toNat, by omega⟩
    have hj : j < k := by omega
    cases hj' : tape (h + j) with
    | false => exact absurd hj' (hmin j hj)
    | true => rfl
  refine ⟨k + 1, ?_, ?_⟩
  · rw [run_succ, hsweep]
    simp [step, hk]; rfl
  · rw [run_succ, hsweep]
    simp only [step, hk, addOne_false]
    have hnotmem : h + (k : ℤ) ∉ {p | tape p = true} := by simp [hk]
    have : {p | Function.update tape (h + k) true p = true} = insert (h + (k : ℤ)) {p | tape p = true} := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
      by_cases hp : p = h + k
      · subst hp; simp
      · rw [Function.update_of_ne hp]; simp [hp]
    rw [this, Set.ncard_insert_of_notMem hnotmem hfin]

/-- The extended machine of the paper: `M` followed by the extra card. -/
theorem haltsWithScore_seq_addOne {M : Machine n} {s : ℕ} (hn : 0 < n) (h : HaltsWithScore M s) :
    HaltsWithScore (seq M addOne) (s + 1) := by
  obtain ⟨t₁, ht₁, hs⟩ := h
  obtain ⟨t, ht, hact⟩ := exists_first_halt ⟨t₁, ht₁⟩
  -- the ones at time t₁ are those at time t
  have hs' : (ones (run M (init n) t)).ncard = s := by
    rw [run_eq_of_halted ht ht₁]
    exact hs
  have hinit : init (n + 1) = emb₁ 1 (init n) := by
    unfold init emb₁ startState secondStart
    have hn1 : 0 < n + 1 := by omega
    simp only [dif_pos hn, dif_pos hn1]
    rfl
  have hfin : {p | (run M (init n) t).tape p = true}.Finite := ones_finite M t
  obtain ⟨t₂, ht₂, hcount⟩ := addOne_adds (run M (init n) t).tape (run M (init n) t).head hfin
  refine ⟨t + t₂, ?_, ?_⟩
  · rw [hinit, run_add, run_emb₁ M addOne _ t hact, emb₁_halted 1 ht, run_emb₂]
    have hstart : startState 1 = some ⟨0, by norm_num⟩ := by simp [startState]
    rw [hstart]
    simp only [emb₂]
    rw [ht₂]; rfl
  · rw [hinit, run_add, run_emb₁ M addOne _ t hact, emb₁_halted 1 ht, run_emb₂]
    have hstart : startState 1 = some ⟨0, by norm_num⟩ := by simp [startState]
    rw [hstart]
    show {p | (run addOne ⟨some ⟨0, by norm_num⟩, (run M (init n) t).head, (run M (init n) t).tape⟩ t₂).tape p = true}.ncard = s + 1
    rw [hcount]
    exact congrArg (· + 1) hs'

/-- `Σ(n) < Σ(n+1)` for `n ≥ 1`. -/
theorem sigma_lt_succ (hn : 0 < n) : sigma n < sigma (n + 1) := by
  obtain ⟨M, hM⟩ := exists_sigma_witness hn
  have := le_sigma (haltsWithScore_seq_addOne hn hM)
  omega

/-! ### `SC` and `H` -/

/-- The squares scanned in an active state during the first `t` steps. -/
def scanned (M : Machine n) (t : ℕ) : Set ℤ :=
  {p | ∃ s < t, (run M (init n) s).state ≠ none ∧ (run M (init n) s).head = p}

/-- Every one on the tape at time `t` was written while scanning that square. -/
theorem ones_subset_scanned (M : Machine n) (t : ℕ) : ones (run M (init n) t) ⊆ scanned M t := by
  induction t with
  | zero => intro p hp; simp [ones, init, blank] at hp
  | succ t ih =>
    intro p hp
    simp only [ones, Set.mem_setOf_eq, run_succ, step] at hp
    cases hs : (run M (init n) t).state with
    | none =>
      rw [hs] at hp
      obtain ⟨s, hst, hs1, hs2⟩ := ih hp
      exact ⟨s, by omega, hs1, hs2⟩
    | some q =>
      rw [hs] at hp
      simp only at hp
      by_cases hpq : p = (run M (init n) t).head
      · exact ⟨t, by omega, by rw [hs]; exact Option.some_ne_none q, hpq.symm⟩
      · rw [Function.update_of_ne hpq] at hp
        obtain ⟨s, hst, hs1, hs2⟩ := ih hp
        exact ⟨s, by omega, hs1, hs2⟩

theorem scanned_finite (M : Machine n) (t : ℕ) : (scanned M t).Finite := by
  apply Set.Finite.subset (Set.finite_Icc (0 - (t : ℤ)) (0 + t))
  intro p hp
  obtain ⟨s, hst, -, hs2⟩ := hp
  have h := (ones_subset_run (M := M) (c := init n) (a := 0) (b := 0)
    (fun p hp => by simp [init, blank] at hp) (by simp [init]) s).2
  rw [hs2] at h
  exact Set.mem_Icc.2 ⟨by have := h.1; linarith, by have := h.2; linarith⟩

theorem ncard_scanned_le (M : Machine n) (t : ℕ) : (scanned M t).ncard ≤ t := by
  induction t with
  | zero =>
    have : scanned M 0 = ∅ := by ext p; simp [scanned]
    rw [this, Set.ncard_empty]
  | succ t ih =>
    have hsub : scanned M (t + 1) ⊆ insert (run M (init n) t).head (scanned M t) := by
      intro p ⟨s, hst, hs1, hs2⟩
      rcases Nat.lt_or_ge s t with h | h
      · exact Set.mem_insert_of_mem _ ⟨s, h, hs1, hs2⟩
      · have : s = t := by omega
        subst this; rw [← hs2]; exact Set.mem_insert _ _
    calc (scanned M (t + 1)).ncard ≤ (insert (run M (init n) t).head (scanned M t)).ncard :=
          Set.ncard_le_ncard hsub ((scanned_finite M t).insert _)
      _ ≤ (scanned M t).ncard + 1 := Set.ncard_insert_le _ _
      _ ≤ t + 1 := by omega

/-- The number of squares scanned in an active state by `M` before halting (for a halting
machine, all scanning happens before the halting time). -/
noncomputable def scanCount (M : Machine n) : ℕ := (scanned M (haltTime M)).ncard

/-- `SC(n)`. -/
noncomputable def SC (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun M : Machine n => Halts M)).sup scanCount

theorem le_SC {M : Machine n} (h : Halts M) : scanCount M ≤ SC n := by
  apply Finset.le_sup (f := scanCount)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact h

/-- `Σ(n) ≤ SC(n)`: the paper's (1), first half. -/
theorem sigma_le_SC (n : ℕ) : sigma n ≤ SC n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [sigma]
    apply Finset.sup_le
    intro M _
    have hz : HaltsWithScore M 0 := ⟨0, by simp [init, startState], by simp [init, ones, blank]⟩
    rw [score_spec hz]
    exact Nat.zero_le _
  · obtain ⟨M, t, ht, hs⟩ := exists_sigma_witness hn
    have hH : Halts M := ⟨t, ht⟩
    have hex := haltsInExactly_haltTime hH
    rw [run_eq_of_halted ht hex.1] at hs
    calc sigma n = (ones (run M (init n) (haltTime M))).ncard := hs.symm
      _ ≤ (scanned M (haltTime M)).ncard :=
          Set.ncard_le_ncard (ones_subset_scanned M _) (scanned_finite M _)
      _ ≤ SC n := le_SC hH

/-- `SC(n) ≤ SH(n)`: the paper's (1), second half. -/
theorem SC_le_SH (n : ℕ) : SC n ≤ SH n := by
  rw [SC]
  apply Finset.sup_le
  intro M hM
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
  calc scanCount M = (scanned M (haltTime M)).ncard := rfl
    _ ≤ haltTime M := ncard_scanned_le M _
    _ ≤ SH n := le_SH (haltsInExactly_haltTime hM)

/-- `SC` and `SH` are not Turing computable. -/
theorem SC_not_computable : ¬ TMComputable SC := fun h =>
  no_computable_bound h (fun n => sigma_le_SC n)

theorem SH_not_computable : ¬ TMComputable SH := fun h =>
  no_computable_bound h (fun n => sigma_le_SH n)

/-- `H(n)`: the number of halting `n`-state machines. -/
noncomputable def H (n : ℕ) : ℕ := (Finset.univ.filter (fun M : Machine n => Halts M)).card

/-- The actions form `Bool × Move × Option (Fin n)`. -/
def Action.equiv (n : ℕ) : Action n ≃ Bool × Move × Option (Fin n) where
  toFun a := (a.write, a.move, a.next)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_move : Fintype.card Move = 2 := rfl

theorem card_action (n : ℕ) : Fintype.card (Action n) = 4 * n + 4 := by
  rw [Fintype.card_congr (Action.equiv n), Fintype.card_prod, Fintype.card_prod, card_move,
    Fintype.card_bool, Fintype.card_option, Fintype.card_fin]
  ring

/-- A machine is its table. -/
def Machine.equiv (n : ℕ) : Machine n ≃ (Fin n → Bool → Action n) where
  toFun M := M.card
  invFun c := ⟨c⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The number of labelled `n`-state transition tables is `(4n+4)^(2n)`. -/
theorem card_machine (n : ℕ) : Fintype.card (Machine n) = (4 * n + 4) ^ (2 * n) := by
  rw [Fintype.card_congr (Machine.equiv n), Fintype.card_fun, Fintype.card_fun, card_action,
    Fintype.card_bool, Fintype.card_fin, ← pow_mul, mul_comm]

/-- The machine that never halts (every card moves right into state `1`). -/
def looper (n : ℕ) (hn : 0 < n) : Machine n where
  card _ _ := ⟨false, .R, some ⟨0, hn⟩⟩

theorem looper_run (n : ℕ) (hn : 0 < n) (t : ℕ) :
    run (looper n hn) (init n) t = ⟨some ⟨0, hn⟩, t, blank⟩ := by
  induction t with
  | zero => simp [init, startState, dif_pos hn]
  | succ t ih =>
    rw [run_succ, ih]
    simp only [step, looper, Config.mk.injEq]
    refine ⟨by trivial, by simp [Move.apply], ?_⟩
    funext q
    by_cases hq : q = (t : ℤ)
    · subst hq; simp [blank]
    · rw [Function.update_of_ne hq]

theorem looper_not_halts (n : ℕ) (hn : 0 < n) : ¬ Halts (looper n hn) := by
  rintro ⟨t, ht⟩
  rw [looper_run] at ht
  exact Option.some_ne_none _ ht

/-- The paper's (2): `H(n) < (4n+4)^(2n)` for `n ≥ 1`. -/
theorem H_lt (n : ℕ) (hn : 0 < n) : H n < (4 * n + 4) ^ (2 * n) := by
  rw [← card_machine, ← Finset.card_univ, H]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
  exact ⟨looper n hn, Finset.mem_univ _, by simp [looper_not_halts]⟩

theorem H_le (n : ℕ) : H n ≤ (4 * n + 4) ^ (2 * n) := by
  rw [← card_machine, ← Finset.card_univ, H]
  exact Finset.card_le_card (Finset.filter_subset _ _)

end Jones1974
