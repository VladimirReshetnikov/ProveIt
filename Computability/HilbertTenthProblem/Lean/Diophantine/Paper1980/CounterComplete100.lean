import Diophantine.Paper1980.CounterSound100

/-!
# Accepting computations are serial runs of the compiled program

`EXPLORATION_THREE_RAW_COUNTER_UNIVERSAL_COMPILER.md`, §5, the other direction: an accepting
logical computation `(0, (x,0,0)) → … → (ℓ_K, 0)` with `ℓ_K` an accepting halt is laid out as
a serial run of `6 + 6(K + 1)` blocks.  Blocks `0–5` are the prefix; blocks `6 + 6k + j` are
the `j`-th lane-block of the two banks of the `k`-th configuration, entered at the zero branch
of a test exactly when the tested register is zero.  The physical value at the first bank's
lanes is twice the logical one, and at the second bank's lanes it has moved by the first
bank's sign.

`run_of_accepts` proves every field of `Graph.SerialRun` for this layout.
-/

namespace Jones1980

namespace CProgram

/-- A `ReflTransGen` chain as an indexed sequence. -/
theorem exists_seq {α : Type} {rel : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen rel a b) :
    ∃ (K : ℕ) (c : ℕ → α), c 0 = a ∧ c K = b ∧ ∀ k, k < K → rel (c k) (c (k + 1)) := by
  induction h with
  | refl => exact ⟨0, fun _ => a, rfl, rfl, fun k hk => absurd hk (by omega)⟩
  | @tail b1 c' _ hbc ih =>
    obtain ⟨K, c, h0, hK, hs⟩ := ih
    refine ⟨K + 1, fun k => if k ≤ K then c k else c', by simp [h0], by simp, fun k hk => ?_⟩
    by_cases hkK : k + 1 ≤ K
    · simp only [if_pos (show k ≤ K by omega), if_pos hkK]
      exact hs k (by omega)
    · have hk : k = K := by omega
      subst hk
      simp only [le_refl, if_true, if_neg hkK]
      rw [hK]
      exact hbc

variable (M : CProgram)

/-- Which bank pair a configuration uses: `2` for the nonzero branch of a test, else `0`. -/
def kindOf (ℓ : ℕ) (w : Fin 3 → ℕ) : ℕ :=
  match M.code ℓ with
  | .test r _ _ => if w r = 0 then 0 else 2
  | _ => 0

/-- The lane of a block, as a register. -/
def fin3 (n : ℕ) : Fin 3 := ⟨n % 3, Nat.mod_lt _ (by norm_num)⟩

/-- The sign of a lane, as an integer. -/
def sig (s l : ℕ) : ℤ := if M.sgnSL s l = true then 1 else -1

section Layout

variable (x : ℕ) (L : ℕ → ℕ) (W : ℕ → Fin 3 → ℕ)

/-- The first slot of configuration `k`. -/
def slotAt (k : ℕ) : ℕ := 2 + 4 * L k + M.kindOf (L k) (W k)

/-- The states of the laid-out run. -/
def runSt (b : ℕ) : ℕ :=
  if b < 6 then b else 3 * (M.slotAt L W ((b - 6) / 6) + (b - 6) % 6 / 3) + (b - 6) % 6 % 3

/-- The values of the laid-out run. -/
def runVal (b : ℕ) : ℕ :=
  if b < 3 then (if b = 0 then 2 * x else 0)
  else if b < 6 then (if b = 3 then 2 * x + 1 else 1)
  else if (b - 6) % 6 < 3 then 2 * W ((b - 6) / 6) (fin3 ((b - 6) % 6))
  else (2 * (W ((b - 6) / 6) (fin3 ((b - 6) % 6)) : ℤ)
    + M.sig (M.slotAt L W ((b - 6) / 6)) ((b - 6) % 6 % 3)).toNat

theorem runSt_block {k j : ℕ} (hj : j < 6) :
    M.runSt L W (6 + 6 * k + j) = 3 * (M.slotAt L W k + j / 3) + j % 3 := by
  unfold runSt
  rw [if_neg (by omega), show (6 + 6 * k + j - 6) / 6 = k by omega,
    show (6 + 6 * k + j - 6) % 6 = j by omega]

theorem runVal_lo {k j : ℕ} (hj : j < 3) :
    M.runVal x L W (6 + 6 * k + j) = 2 * W k (fin3 j) := by
  unfold runVal
  rw [if_neg (by omega), if_neg (by omega), show (6 + 6 * k + j - 6) / 6 = k by omega,
    show (6 + 6 * k + j - 6) % 6 = j by omega, if_pos hj]

theorem runVal_hi {k j : ℕ} (hj : 3 ≤ j) (hj6 : j < 6) :
    M.runVal x L W (6 + 6 * k + j)
      = (2 * (W k (fin3 j) : ℤ) + M.sig (M.slotAt L W k) (j % 3)).toNat := by
  unfold runVal
  rw [if_neg (by omega), if_neg (by omega), show (6 + 6 * k + j - 6) / 6 = k by omega,
    show (6 + 6 * k + j - 6) % 6 = j by omega, if_neg (by omega)]

end Layout

/-- The shapes of a logical step. -/
theorem step_cases {ℓ ℓ' : ℕ} {w w' : Fin 3 → ℕ} (h : M.Step (ℓ, w) (ℓ', w')) :
    ℓ < M.len ∧
    ((∃ r, M.code ℓ = .inc r ℓ' ∧ w' = Function.update w r (w r + 1) ∧ M.kindOf ℓ w = 0) ∨
     (∃ r nz, M.code ℓ = .test r ℓ' nz ∧ w r = 0 ∧ w' = w ∧ M.kindOf ℓ w = 0) ∨
     (∃ r z, M.code ℓ = .test r z ℓ' ∧ w r ≠ 0 ∧ w' = Function.update w r (w r - 1) ∧
        M.kindOf ℓ w = 2)) := by
  generalize hp : (ℓ, w) = p at h
  generalize hq : (ℓ', w') = q at h
  cases h with
  | inc hℓ hc =>
    simp only [Prod.mk.injEq] at hp hq
    obtain ⟨rfl, rfl⟩ := hp
    obtain ⟨rfl, rfl⟩ := hq
    refine ⟨hℓ, Or.inl ⟨_, hc, rfl, ?_⟩⟩
    unfold kindOf; rw [hc]
  | zero hℓ hc hv =>
    simp only [Prod.mk.injEq] at hp hq
    obtain ⟨rfl, rfl⟩ := hp
    obtain ⟨rfl, rfl⟩ := hq
    refine ⟨hℓ, Or.inr (Or.inl ⟨_, _, hc, hv, rfl, ?_⟩)⟩
    unfold kindOf; rw [hc]; simp [hv]
  | dec hℓ hc hv =>
    simp only [Prod.mk.injEq] at hp hq
    obtain ⟨rfl, rfl⟩ := hp
    obtain ⟨rfl, rfl⟩ := hq
    refine ⟨hℓ, Or.inr (Or.inr ⟨_, _, hc, hv, rfl, ?_⟩)⟩
    unfold kindOf; rw [hc]; simp [hv]

theorem fin3_val (n : ℕ) : (fin3 n : ℕ) = n % 3 := rfl

theorem fin3_eq {j : ℕ} {i : Fin 3} : fin3 j = i ↔ j % 3 = i := by
  unfold fin3
  constructor
  · intro h; rw [← h]
  · intro h; exact Fin.ext h

theorem zeroSL_bank {ℓ kd l : ℕ} (hkd : kd < 4) (h : M.zeroSL (2 + 4 * ℓ + kd) l = true) :
    kd = 0 ∧ ((∃ r z nz, M.code ℓ = .test r z nz ∧ l = r.val) ∨ M.code ℓ = .accept) := by
  rw [M.zeroSL_slot hkd] at h
  cases hc : M.code ℓ with
  | test r z nz => rw [hc] at h; simp at h; exact ⟨h.1, Or.inl ⟨r, z, nz, rfl, h.2⟩⟩
  | accept => rw [hc] at h; simp at h; exact ⟨h, Or.inr rfl⟩
  | inc r nx => rw [hc] at h; simp at h
  | stop => rw [hc] at h; simp at h

theorem sig_slot {ℓ kd l : ℕ} (hkd : kd < 4) :
    M.sig (2 + 4 * ℓ + kd) l = if (match M.code ℓ with
      | .inc r _ => kd == 0 || (kd == 1 && l == r.val)
      | .test r _ _ => kd == 0 || (kd == 2 && l != r.val)
      | .accept => kd == 0
      | .stop => false) = true then 1 else -1 := by
  unfold sig
  rw [M.sgnSL_slot hkd]
  rfl

set_option maxHeartbeats 4000000 in
/-- **§5, completeness.**  An accepting computation of the program, laid out block by block,
is an accepting serial run of its compiled graph. -/
theorem run_of_seq {x K : ℕ} {L : ℕ → ℕ} {W : ℕ → Fin 3 → ℕ} (hL0 : L 0 = 0)
    (hW0 : W 0 = start x) (hstep : ∀ k, k < K → M.Step (L k, W k) (L (k + 1), W (k + 1)))
    (hlenK : L K < M.len) (hacc : M.code (L K) = .accept) (hWK : W K = fun _ => 0)
    (hWK1 : W (K + 1) = fun _ => 0) :
    M.graph.SerialRun x (6 + 6 * (K + 1)) (M.runSt L W) (M.runVal x L W) := by
  -- ## per-configuration facts
  have hlen : ∀ k, k ≤ K → L k < M.len := fun k hk => by
    rcases Nat.lt_or_ge k K with h | h
    · exact (M.step_cases (hstep k h)).1
    · rw [show k = K by omega]; exact hlenK
  have hslot_lt : ∀ k, k ≤ K → M.slotAt L W k + 1 < 2 + 4 * M.len := fun k hk => by
    have h1 := hlen k hk
    have h2 : M.kindOf (L k) (W k) ≤ 2 := by
      unfold kindOf; split <;> (try split) <;> omega
    unfold slotAt; omega
  have hkindK : M.kindOf (L K) (W K) = 0 := by unfold kindOf; rw [hacc]
  -- the entry bank of every configuration
  have hentry : ∀ k, k ≤ K → M.entry (L k) (M.slotAt L W k) = true := fun k hk => by
    unfold entry slotAt
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hlen k hk, ?_⟩
    rcases Nat.lt_or_ge k K with h | h
    · rcases (M.step_cases (hstep k h)).2 with ⟨r, hc, -, hkd⟩ | ⟨r, nz, hc, -, -, hkd⟩ |
        ⟨r, z, hc, -, -, hkd⟩ <;> rw [hkd, hc] <;> simp
    · have hk' : k = K := by omega
      subst hk'
      rw [hkindK, hacc]; simp
  -- the first bank leads to the second
  have hbank1 : ∀ k, k ≤ K → M.bankNext (M.slotAt L W k) (M.slotAt L W k + 1) = true :=
    fun k hk => by
    have hkd : M.kindOf (L k) (W k) < 4 := by
      unfold kindOf; split <;> (try split) <;> omega
    unfold slotAt
    rw [M.bankNext_slot hkd]
    rcases Nat.lt_or_ge k K with h | h
    · rcases (M.step_cases (hstep k h)).2 with ⟨r, hc, -, hkd'⟩ | ⟨r, nz, hc, -, -, hkd'⟩ |
        ⟨r, z, hc, -, -, hkd'⟩ <;> rw [hc] <;> simp [hkd']
    · have hk' : k = K := by omega
      subst hk'
      rw [hacc]; simp [hkindK]
  -- the second bank leads to the next configuration's entry
  have hbank2 : ∀ k, k < K →
      M.bankNext (M.slotAt L W k + 1) (M.slotAt L W (k + 1)) = true := fun k hk => by
    have hent := hentry (k + 1) (by omega)
    rcases (M.step_cases (hstep k hk)).2 with ⟨r, hc, -, hkd⟩ | ⟨r, nz, hc, -, -, hkd⟩ |
        ⟨r, z, hc, -, -, hkd⟩
    · have e := M.bankNext_slot (ℓ := L k) (k := 1) (t := M.slotAt L W (k + 1)) (by norm_num)
      rw [show 2 + 4 * L k + 1 = M.slotAt L W k + 1 by unfold slotAt; rw [hkd]] at e
      rw [e, hc]; simp [hent]
    · have e := M.bankNext_slot (ℓ := L k) (k := 1) (t := M.slotAt L W (k + 1)) (by norm_num)
      rw [show 2 + 4 * L k + 1 = M.slotAt L W k + 1 by unfold slotAt; rw [hkd]] at e
      rw [e, hc]; simp [hent]
    · have e := M.bankNext_slot (ℓ := L k) (k := 3) (t := M.slotAt L W (k + 1)) (by norm_num)
      rw [show 2 + 4 * L k + 3 = M.slotAt L W k + 1 by unfold slotAt; rw [hkd]] at e
      rw [e, hc]; simp [hent]
  have hnv : ∀ k, k ≤ K → ∀ j, j < 6 → M.runSt L W (6 + 6 * k + j) < M.nv := fun k hk j hj => by
    rw [M.runSt_block L W hj]
    have := hslot_lt k hk
    unfold nv
    omega
  -- ## the adjacency of the laid-out states
  have hadj : ∀ v w, v < M.nv → w < M.nv →
      (v % 3 = 2 → w % 3 = 0 ∧ M.bankNext (v / 3) (w / 3) = true) →
      (v % 3 ≠ 2 → w = v + 1) → M.adj v w = true := by
    intro v w hv hw h1 h2
    unfold adj
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨hv, hw⟩, ?_⟩
    by_cases h : v % 3 = 2
    · rw [if_pos h]; simp [(h1 h).1, (h1 h).2]
    · rw [if_neg h]; simp [h2 h]
  have hnv6 : 6 ≤ M.nv := by unfold nv; omega
  have hkd2 : ∀ k, M.kindOf (L k) (W k) ≤ 2 := fun k => by
    unfold kindOf; split <;> (try split) <;> omega
  have hnotacc : ∀ k, k < K → M.code (L k) ≠ .accept := fun k hk hc => by
    rcases (M.step_cases (hstep k hk)).2 with ⟨r, hc2, -⟩ | ⟨r, nz, hc2, -⟩ | ⟨r, z, hc2, -⟩ <;>
      rw [hc] at hc2 <;> exact CInstr.noConfusion hc2
  -- ## the signs of the laid-out banks
  have hsig1 : ∀ k, k ≤ K → ∀ i : Fin 3,
      M.sig (M.slotAt L W k) i = 1 ∨ (M.sig (M.slotAt L W k) i = -1 ∧ W k i ≠ 0) := by
    intro k hk i
    have e := M.sig_slot (ℓ := L k) (kd := M.kindOf (L k) (W k)) (l := i)
      (by have := hkd2 k; omega)
    unfold slotAt
    rw [e]
    rcases Nat.lt_or_ge k K with h | h
    · rcases (M.step_cases (hstep k h)).2 with ⟨r, hc, -, hkd⟩ | ⟨r, nz, hc, -, -, hkd⟩ |
          ⟨r, z, hc, hr, -, hkd⟩
      · left; rw [hc, hkd]; simp
      · left; rw [hc, hkd]; simp
      · rw [hc, hkd]
        by_cases hir : i = r
        · subst hir; right; simp [hr]
        · left
          have hne : (i : ℕ) ≠ (r : ℕ) := fun h => hir (Fin.ext h)
          simp [hne]
    · have hkK : k = K := by omega
      subst hkK
      left; rw [hacc, hkindK]; simp
  have hsig12 : ∀ k, k ≤ K → ∀ i : Fin 3, 2 * (W (k + 1) i : ℤ)
      = 2 * W k i + M.sig (M.slotAt L W k) i + M.sig (M.slotAt L W k + 1) i := by
    intro k hk i
    have hkd4 := hkd2 k
    have e1 := M.sig_slot (ℓ := L k) (kd := M.kindOf (L k) (W k)) (l := i) (by omega)
    have e2 := M.sig_slot (ℓ := L k) (kd := M.kindOf (L k) (W k) + 1) (l := i) (by omega)
    rw [← add_assoc] at e2
    unfold slotAt
    rw [e1, e2]
    rcases Nat.lt_or_ge k K with h | h
    · rcases (M.step_cases (hstep k h)).2 with ⟨r, hc, hw, hkd⟩ | ⟨r, nz, hc, -, hw, hkd⟩ |
          ⟨r, z, hc, hr, hw, hkd⟩
      · rw [hc, hkd, hw]
        by_cases hir : i = r
        · subst hir; simp; ring
        · have hne : (i : ℕ) ≠ (r : ℕ) := fun h => hir (Fin.ext h)
          simp [hne, Function.update_of_ne hir]
      · rw [hc, hkd, hw]; simp
      · rw [hc, hkd, hw]
        by_cases hir : i = r
        · subst hir; simp; omega
        · have hne : (i : ℕ) ≠ (r : ℕ) := fun h => hir (Fin.ext h)
          simp [hne, Function.update_of_ne hir]
    · have hkK : k = K := by omega
      subst hkK
      rw [hacc, hkindK, hWK, hWK1]; simp
  refine
    { three_le := by omega
      start := by unfold runSt; simp
      states := fun b hb => ?_
      step := fun b hb => ?_
      wrap := ?_
      init := by unfold runVal; simp
      update := fun b hb => ?_
      zero_test := fun b hb hz => ?_
      final := ?_ }
  -- states
  · rcases Nat.lt_or_ge b 6 with h6 | h6
    · show M.runSt L W b < M.nv
      unfold runSt; rw [if_pos h6]; omega
    · obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 6 ∧ b = 6 + 6 * k + j :=
        ⟨(b - 6) / 6, (b - 6) % 6, Nat.mod_lt _ (by norm_num), by omega⟩
      exact hnv k (by omega) j hj
  -- step
  · show M.adj (M.runSt L W b) (M.runSt L W (b + 1)) = true
    rcases Nat.lt_or_ge b 5 with h5 | h5
    · have e0 : M.runSt L W b = b := by unfold runSt; rw [if_pos (by omega)]
      have e1 : M.runSt L W (b + 1) = b + 1 := by unfold runSt; rw [if_pos (by omega)]
      rw [e0, e1]
      refine hadj _ _ (by omega) (by omega) (fun h => ?_) (fun _ => rfl)
      have hb2 : b = 2 := by omega
      subst hb2
      unfold bankNext; simp
    · rcases Nat.eq_or_lt_of_le h5 with h5 | h5
      · subst h5
        have e0 : M.runSt L W 5 = 5 := by unfold runSt; simp
        have e1 := M.runSt_block L W (k := 0) (j := 0) (by norm_num)
        simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_div] at e1
        rw [e0, e1]
        refine hadj _ _ (by omega) (by have := hslot_lt 0 (by omega); unfold nv; omega)
          (fun _ => ⟨by omega, ?_⟩) (fun h => absurd rfl h)
        rw [show (3 * M.slotAt L W 0 + 0 % 3) / 3 = M.slotAt L W 0 by omega]
        unfold bankNext
        simp only [show (5 : ℕ) / 3 = 1 from rfl, one_ne_zero, if_false, if_true]
        have := hentry 0 (by omega)
        rwa [hL0] at this
      · obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 6 ∧ b = 6 + 6 * k + j :=
          ⟨(b - 6) / 6, (b - 6) % 6, Nat.mod_lt _ (by norm_num), by omega⟩
        have hkK : k ≤ K := by omega
        rcases Nat.lt_or_ge j 5 with hj5 | hj5
        · have e1 := M.runSt_block L W (k := k) (j := j + 1) (by omega)
          rw [show 6 + 6 * k + j + 1 = 6 + 6 * k + (j + 1) by ring, e1, M.runSt_block L W hj]
          have hs := hslot_lt k hkK
          refine hadj _ _ (by rw [← M.runSt_block L W hj]; exact hnv k hkK j hj)
            (by unfold nv; interval_cases j <;> omega)
            (fun h => ?_) (fun h => by interval_cases j <;> simp_all <;> omega)
          have hj2 : j = 2 := by interval_cases j <;> omega
          subst hj2
          refine ⟨by omega, ?_⟩
          rw [show (3 * (M.slotAt L W k + 2 / 3) + 2 % 3) / 3 = M.slotAt L W k by omega,
            show (3 * (M.slotAt L W k + (2 + 1) / 3) + (2 + 1) % 3) / 3
              = M.slotAt L W k + 1 by omega]
          exact hbank1 k hkK
        · have hj5e : j = 5 := by omega
          subst hj5e
          have hkK2 : k < K := by omega
          have e1 := M.runSt_block L W (k := k + 1) (j := 0) (by norm_num)
          rw [show 6 + 6 * k + 5 + 1 = 6 + 6 * (k + 1) + 0 by ring, e1, M.runSt_block L W hj]
          refine hadj _ _ (by rw [← M.runSt_block L W hj]; exact hnv k hkK 5 hj)
            (by have := hslot_lt (k + 1) (by omega); unfold nv; omega)
            (fun _ => ⟨by omega, ?_⟩) (fun h => absurd (by omega) h)
          rw [show (3 * (M.slotAt L W k + 5 / 3) + 5 % 3) / 3 = M.slotAt L W k + 1 by omega,
            show (3 * (M.slotAt L W (k + 1) + 0 / 3) + 0 % 3) / 3 = M.slotAt L W (k + 1) by omega]
          exact hbank2 k hkK2
  -- wrap
  · show M.adj (M.runSt L W (6 + 6 * (K + 1) - 1)) 0 = true
    have hK5 := hnv K le_rfl 5 (by norm_num)
    rw [show 6 + 6 * (K + 1) - 1 = 6 + 6 * K + 5 by omega]
    rw [M.runSt_block L W (by norm_num)] at hK5 ⊢
    refine hadj _ _ hK5 (by omega) (fun _ => ⟨rfl, ?_⟩) (fun h => absurd (by omega) h)
    rw [show (3 * (M.slotAt L W K + 5 / 3) + 5 % 3) / 3 = M.slotAt L W K + 1 by omega]
    unfold slotAt
    rw [hkindK, Nat.add_zero, M.bankNext_slot (k := 1) (by norm_num), hacc]
    simp
  -- update
  · show (M.runVal x L W (b + 3) : ℤ) = M.runVal x L W b
      + (if M.sgnSL (M.runSt L W b / 3) (M.runSt L W b % 3) = true then 1 else -1)
    rcases Nat.lt_or_ge b 6 with h6 | h6
    · have e0 : M.runSt L W b = b := by unfold runSt; rw [if_pos h6]
      rw [e0]
      rcases Nat.lt_or_ge b 3 with h3 | h3
      · unfold runVal
        interval_cases b <;> simp [sgnSL]
      · have e1 := M.runVal_lo x L W (k := 0) (j := b - 3) (by omega)
        rw [show 6 + 6 * 0 + (b - 3) = b + 3 by omega, hW0] at e1
        rw [e1]
        unfold runVal
        interval_cases b <;> simp [sgnSL, start, fin3]
    · obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 6 ∧ b = 6 + 6 * k + j :=
        ⟨(b - 6) / 6, (b - 6) % 6, Nat.mod_lt _ (by norm_num), by omega⟩
      have hkK : k ≤ K := by omega
      rw [M.runSt_block L W hj]
      rcases Nat.lt_or_ge j 3 with hj3 | hj3
      · rw [show 6 + 6 * k + j + 3 = 6 + 6 * k + (j + 3) by ring, M.runVal_hi x L W (by omega)
          (by omega), M.runVal_lo x L W hj3,
          show (3 * (M.slotAt L W k + j / 3) + j % 3) / 3 = M.slotAt L W k by omega,
          show (3 * (M.slotAt L W k + j / 3) + j % 3) % 3 = j by omega,
          show (j + 3) % 3 = j by omega]
        have hf : fin3 (j + 3) = fin3 j := by unfold fin3; congr 1; omega
        have hji : (fin3 j : ℕ) = j := by unfold fin3; simp; omega
        rw [hf]
        have hs := hsig1 k hkK (fin3 j)
        rw [hji] at hs
        show _ = _ + M.sig (M.slotAt L W k) j
        rcases hs with hs | ⟨hs, hne⟩
        · rw [hs]; push_cast; omega
        · rw [hs]; push_cast; omega
      · rw [show 6 + 6 * k + j + 3 = 6 + 6 * (k + 1) + (j - 3) by omega,
          M.runVal_lo x L W (by omega), M.runVal_hi x L W hj3 hj,
          show (3 * (M.slotAt L W k + j / 3) + j % 3) / 3 = M.slotAt L W k + 1 by omega,
          show (3 * (M.slotAt L W k + j / 3) + j % 3) % 3 = j % 3 by omega]
        have hf : fin3 (j - 3) = fin3 j := by unfold fin3; congr 1; omega
        rw [hf]
        have hji : (fin3 j : ℕ) = j % 3 := rfl
        have h12 := hsig12 k hkK (fin3 j)
        have hs := hsig1 k hkK (fin3 j)
        rw [hji] at h12 hs
        show _ = _ + M.sig (M.slotAt L W k + 1) (j % 3)
        rcases hs with hs | ⟨hs, hne⟩
        · rw [hs] at h12 ⊢; push_cast; omega
        · rw [hs] at h12 ⊢; push_cast; omega
  -- zero tests
  · have hz2 : M.zeroSL (M.runSt L W b / 3) (M.runSt L W b % 3) = true := by
      have : (!M.zeroSL (M.runSt L W b / 3) (M.runSt L W b % 3)) = false := hz
      simpa using this
    rcases Nat.lt_or_ge b 6 with h6 | h6
    · have e0 : M.runSt L W b = b := by unfold runSt; rw [if_pos h6]
      rw [e0] at hz2
      unfold zeroSL at hz2
      rw [if_pos (by omega)] at hz2
      simp at hz2
    · obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 6 ∧ b = 6 + 6 * k + j :=
        ⟨(b - 6) / 6, (b - 6) % 6, Nat.mod_lt _ (by norm_num), by omega⟩
      have hkK : k ≤ K := by omega
      rw [M.runSt_block L W hj, show (3 * (M.slotAt L W k + j / 3) + j % 3) / 3
        = 2 + 4 * L k + (M.kindOf (L k) (W k) + j / 3) by unfold slotAt; omega,
        show (3 * (M.slotAt L W k + j / 3) + j % 3) % 3 = j % 3 by omega] at hz2
      obtain ⟨hkz, hcase⟩ := M.zeroSL_bank (by have := hkd2 k; omega) hz2
      have hj3 : j < 3 := by omega
      rw [M.runVal_lo x L W hj3]
      rcases hcase with ⟨r, z, nz, hc, hjr⟩ | hc
      · have hk0 : M.kindOf (L k) (W k) = 0 := by omega
        unfold kindOf at hk0
        simp only [hc] at hk0
        have hwr : W k r = 0 := by
          by_contra hne; rw [if_neg hne] at hk0; omega
        have hf : fin3 j = r := Fin.ext (by unfold fin3; simp; omega)
        rw [hf, hwr]
      · have hkK2 : k = K := by
          by_contra hne
          exact hnotacc k (by omega) hc
        subst hkK2
        rw [hWK]
        rfl
  -- final
  · refine ⟨?_, ?_, ?_⟩
    · have e := M.runVal_lo x L W (k := K + 1) (j := 0) (by norm_num)
      rw [Nat.add_zero] at e
      rw [e, hWK1]
      rfl
    · have e := M.runVal_lo x L W (k := K + 1) (j := 1) (by norm_num)
      rw [e, hWK1]
      rfl
    · have e := M.runVal_lo x L W (k := K + 1) (j := 2) (by norm_num)
      rw [e, hWK1]
      rfl

/-- **§5, completeness.**  A program that accepts `x` has an accepting serial run of its
compiled graph on `x`. -/
theorem run_of_accepts {x : ℕ} (h : M.Accepts x) :
    ∃ u st val, 2 ∣ u ∧ M.graph.SerialRun x u st val := by
  obtain ⟨ℓ, hℓ, hc, hreach⟩ := h
  obtain ⟨K, c, h0, hK, hs⟩ := exists_seq hreach
  refine ⟨_, _, _, ⟨3 + 3 * (K + 1), by ring⟩, M.run_of_seq (x := x) (K := K) (L := fun k => (c k).1)
    (W := fun k => if k ≤ K then (c k).2 else fun _ => 0) ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · simp [h0]
  · simp [h0]
  · intro k hk
    have := hs k hk
    simp only [if_pos (show k ≤ K by omega), if_pos (show k + 1 ≤ K by omega)]
    exact this
  · simp [hK, hℓ]
  · simp [hK, hc]
  · simp [hK]
  · simp

end CProgram

end Jones1980
