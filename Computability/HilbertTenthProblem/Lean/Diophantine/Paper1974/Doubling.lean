import Diophantine.Paper1974.More

/-!
# Jones 1974, the inequality (3): `SC(n) < Σ(3n)`

A halting `n`-state machine `M` is simulated on every other square: the virtual square `i` is
held at the physical square `2i`, and the odd squares record which edges between virtual squares
have been crossed.  The simulating machine uses

* `n` main states `A q`, one for each state of `M`;
* one helper `B (q', d)` for each pair occurring as the target and direction of a nonhalting
  rule of `M` — at most `2n − 1` pairs, since a halting machine has a halting rule;
* one final state `Z`, placed in a helper slot that no rule uses.

`A q` performs the rule of `M` and moves once; the helper writes a `1` on the crossed edge and
moves once more, so two steps of the simulation are one step of `M`.  On the halting rule `A q`
writes `1` (the simulation is over, so the data bit may be changed) and enters `Z`, which runs
right over the ones and appends one more.  If `M` actively scans `k` squares, the `k − 1`
internal edges have all been crossed before the halting step, the last data square carries a
one, and `Z` adds another: at least `k + 1` ones.  Taking `M` with `k = SC(n)` gives (3).
-/

namespace Jones1974

open Classical

variable {n : ℕ}

/-! ### The simulating machine -/

/-- The index of the simulating state `A q`. -/
def aIdx (n : ℕ) (q : Fin n) : Fin (3 * n) := ⟨q.val, by have := q.isLt; omega⟩

/-- The index of the helper state `B (q, d)`; one slot is used for the final state. -/
def bIdx (n : ℕ) (p : Fin n × Move) : Fin (3 * n) :=
  ⟨n + 2 * p.1.val + (if p.2 = Move.R then 1 else 0), by
    have := p.1.isLt; split_ifs <;> omega⟩

theorem aIdx_val (q : Fin n) : (aIdx n q).val = q.val := rfl

theorem bIdx_val (q : Fin n) (d : Move) :
    (bIdx n (q, d)).val = n + 2 * q.val + (if d = Move.R then 1 else 0) := rfl

theorem bIdx_val_L (q : Fin n) : (bIdx n (q, Move.L)).val = n + 2 * q.val := by
  rw [bIdx_val, if_neg (by decide : ¬(Move.L = Move.R))]
  omega

theorem bIdx_val_R (q : Fin n) : (bIdx n (q, Move.R)).val = n + 2 * q.val + 1 := by
  rw [bIdx_val, if_pos rfl]

theorem bIdx_injective : Function.Injective (bIdx n) := by
  rintro ⟨q, d⟩ ⟨q', d'⟩ h
  have hv : (bIdx n (q, d)).val = (bIdx n (q', d')).val := by rw [h]
  have hq := q.isLt
  have hq' := q'.isLt
  cases d <;> cases d' <;>
    simp only [bIdx_val_L, bIdx_val_R] at hv <;>
    first
      | (exfalso; omega)
      | (have : q = q' := Fin.ext (by omega); subst this; rfl)

theorem aIdx_ne_bIdx (q : Fin n) (p : Fin n × Move) : aIdx n q ≠ bIdx n p := by
  obtain ⟨q', d⟩ := p
  intro h
  have hv : (aIdx n q).val = (bIdx n (q', d)).val := by rw [h]
  have := q.isLt
  cases d <;> simp only [aIdx_val, bIdx_val_L, bIdx_val_R] at hv <;> omega

/-- The doubling machine: `A` states simulate, helpers mark the crossed edge, and the helper
slot `z` is used as the final state. -/
def double (M : Machine n) (z : Fin n × Move) : Machine (3 * n) where
  card s b :=
    if hs : s.val < n then
      let q : Fin n := ⟨s.val, hs⟩
      let a := M.card q b
      match a.next with
      | some q' => ⟨a.write, a.move, some (bIdx n (q', a.move))⟩
      | none => ⟨true, a.move, some (bIdx n z)⟩
    else
      let q' : Fin n := ⟨(s.val - n) / 2, by have := s.isLt; omega⟩
      let d : Move := if (s.val - n) % 2 = 1 then Move.R else Move.L
      if (q', d) = z then
        (if b then ⟨true, Move.R, some s⟩ else ⟨true, Move.R, none⟩ : Action (3 * n))
      else ⟨true, d, some (aIdx n q')⟩

theorem double_card_a (M : Machine n) (z : Fin n × Move) (q : Fin n) (b : Bool) :
    (double M z).card (aIdx n q) b =
      match (M.card q b).next with
      | some q' => ⟨(M.card q b).write, (M.card q b).move,
          some (bIdx n (q', (M.card q b).move))⟩
      | none => ⟨true, (M.card q b).move, some (bIdx n z)⟩ := by
  show (if hs : (aIdx n q).val < n then _ else _) = _
  rw [dif_pos (by rw [aIdx_val]; exact q.isLt)]
  simp only [aIdx_val, Fin.eta]

/-- The decoding of a helper slot. -/
theorem double_decode (M : Machine n) (z : Fin n × Move) (q : Fin n) (d : Move) (b : Bool) :
    (double M z).card (bIdx n (q, d)) b =
      (if (q, d) = z then
        (if b then ⟨true, Move.R, some (bIdx n (q, d))⟩ else ⟨true, Move.R, none⟩ :
          Action (3 * n))
      else ⟨true, d, some (aIdx n q)⟩) := by
  have hq := q.isLt
  have hn : ¬ (bIdx n (q, d)).val < n := by cases d <;> simp only [bIdx_val_L, bIdx_val_R] <;> omega
  have hdec : ((bIdx n (q, d)).val - n) / 2 = q.val ∧
      (if ((bIdx n (q, d)).val - n) % 2 = 1 then Move.R else Move.L) = d := by
    cases d <;> simp only [bIdx_val_L, bIdx_val_R] <;>
      refine ⟨by omega, ?_⟩ <;> [rw [if_neg (by omega)]; rw [if_pos (by omega)]]
  show (if hs : (bIdx n (q, d)).val < n then _ else _) = _
  rw [dif_neg hn]
  have hfin : (⟨((bIdx n (q, d)).val - n) / 2, by have := (bIdx n (q, d)).isLt; omega⟩ : Fin n)
      = q := Fin.ext hdec.1
  rw [hfin, hdec.2]

theorem double_card_b (M : Machine n) (z : Fin n × Move) (q : Fin n) (d : Move)
    (hp : (q, d) ≠ z) (b : Bool) :
    (double M z).card (bIdx n (q, d)) b = ⟨true, d, some (aIdx n q)⟩ := by
  rw [double_decode, if_neg hp]

theorem double_card_z (M : Machine n) (z : Fin n × Move) (b : Bool) :
    (double M z).card (bIdx n z) b =
      if b then ⟨true, Move.R, some (bIdx n z)⟩ else ⟨true, Move.R, none⟩ := by
  obtain ⟨z1, z2⟩ := z
  rw [double_decode, if_pos rfl]

/-! ### The simulated tape -/

/-- The edge between the virtual squares `i` and `i + 1` is crossed by a nonhalting step before
time `t`. -/
def crossed (M : Machine n) (t : ℕ) (i : ℤ) : Bool :=
  decide (∃ s < t, (run M (init n) (s + 1)).state ≠ none ∧
    (((run M (init n) s).head = i ∧ (run M (init n) (s + 1)).head = i + 1) ∨
      ((run M (init n) s).head = i + 1 ∧ (run M (init n) (s + 1)).head = i)))

/-- The physical tape after `t` simulated steps: the data on even squares, the edge marks on odd
squares. -/
noncomputable def dtape (M : Machine n) (t : ℕ) : ℤ → Bool := fun y =>
  if y % 2 = 0 then (run M (init n) t).tape (y / 2) else crossed M t ((y - 1) / 2)

theorem dtape_even (M : Machine n) (t : ℕ) (i : ℤ) :
    dtape M t (2 * i) = (run M (init n) t).tape i := by
  unfold dtape
  rw [if_pos (by omega), show (2 * i) / 2 = i by omega]

theorem dtape_odd (M : Machine n) (t : ℕ) (i : ℤ) :
    dtape M t (2 * i + 1) = crossed M t i := by
  unfold dtape
  rw [if_neg (by omega), show (2 * i + 1 - 1) / 2 = i by omega]

theorem crossed_zero (M : Machine n) (i : ℤ) : crossed M 0 i = false := by
  simp [crossed]

theorem crossed_of_lt {M : Machine n} {t t' : ℕ} {i : ℤ} (h : t ≤ t')
    (hc : crossed M t i = true) : crossed M t' i = true := by
  simp only [crossed, decide_eq_true_eq] at hc ⊢
  obtain ⟨s, hs, h1, h2⟩ := hc
  exact ⟨s, by omega, h1, h2⟩

theorem dtape_zero (M : Machine n) : dtape M 0 = blank := by
  funext y
  unfold dtape
  split_ifs
  · show (init n).tape _ = false
    simp [init, blank]
  · rw [crossed_zero]
    rfl

theorem crossed_succ_iff (M : Machine n) (t : ℕ) (i : ℤ) :
    crossed M (t + 1) i = true ↔ crossed M t i = true ∨
      ((run M (init n) (t + 1)).state ≠ none ∧
        (((run M (init n) t).head = i ∧ (run M (init n) (t + 1)).head = i + 1) ∨
         ((run M (init n) t).head = i + 1 ∧ (run M (init n) (t + 1)).head = i))) := by
  simp only [crossed, decide_eq_true_eq]
  constructor
  · rintro ⟨s, hs, h1, h2⟩
    rcases Nat.lt_or_ge s t with h | h
    · exact Or.inl ⟨s, h, h1, h2⟩
    · have : s = t := by omega
      subst this
      exact Or.inr ⟨h1, h2⟩
  · rintro (⟨s, hs, h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨s, by omega, h1, h2⟩
    · exact ⟨t, by omega, h1, h2⟩

/-! ### The simulation -/

/-- The slot `z` is not the target of any nonhalting rule. -/
def Missing (M : Machine n) (z : Fin n × Move) : Prop :=
  ∀ (q : Fin n) (b : Bool) (q' : Fin n), (M.card q b).next = some q' →
    (q', (M.card q b).move) ≠ z

/-- Two steps of the doubling machine are one step of `M`. -/
theorem sim (M : Machine n) (hn : 0 < n) {z : Fin n × Move} (hz : Missing M z) :
    ∀ (t : ℕ) (q : Fin n), (run M (init n) t).state = some q →
      run (double M z) (init (3 * n)) (2 * t)
        = ⟨some (aIdx n q), 2 * (run M (init n) t).head, dtape M t⟩ := by
  intro t
  induction t with
  | zero =>
    intro q hq
    have hq0 : (⟨0, hn⟩ : Fin n) = q := by
      have h : (init n).state = some q := hq
      simp only [init, startState, dif_pos hn, Option.some.injEq] at h
      exact h
    have h3 : (0 : ℕ) < 3 * n := by omega
    show init (3 * n) = _
    simp only [init, Nat.mul_zero, run_zero, Config.mk.injEq]
    refine ⟨?_, by norm_num, (dtape_zero M).symm⟩
    rw [← hq0]
    simp only [startState, dif_pos h3]
    rfl
  | succ t ih =>
    intro q' hq'
    have hact : ∃ q : Fin n, (run M (init n) t).state = some q := by
      cases hs : (run M (init n) t).state with
      | none =>
        rw [run_succ, step_of_halted hs, hs] at hq'
        cases hq'
      | some q => exact ⟨q, rfl⟩
    obtain ⟨q, hq⟩ := hact
    have hD := ih q hq
    set c := run M (init n) t with hc
    set a := M.card q (c.tape c.head) with ha
    have hch : (run M (init n) t).head = c.head := by rw [hc]
    have hstepM : run M (init n) (t + 1)
        = ⟨a.next, a.move.apply c.head, Function.update c.tape c.head a.write⟩ := by
      rw [run_succ, ← hc]
      unfold step
      rw [hq]
    have hnext : a.next = some q' := by
      have h := hq'
      rw [hstepM] at h
      exact h
    have hzne : (q', a.move) ≠ z := hz q (c.tape c.head) q' hnext
    have hbit : dtape M t (2 * c.head) = c.tape c.head := dtape_even M t c.head
    have hs1 : step (double M z) ⟨some (aIdx n q), 2 * c.head, dtape M t⟩
        = ⟨some (bIdx n (q', a.move)), a.move.apply (2 * c.head),
            Function.update (dtape M t) (2 * c.head) a.write⟩ := by
      unfold step
      simp only [hbit, ← ha, double_card_a, hnext]
    have hs2 : ∀ τ : ℤ → Bool, ∀ y : ℤ,
        step (double M z) ⟨some (bIdx n (q', a.move)), y, τ⟩
          = ⟨some (aIdx n q'), a.move.apply y, Function.update τ y true⟩ := by
      intro τ y
      unfold step
      simp only [double_card_b M z q' a.move hzne]
    have hhead : a.move.apply (a.move.apply (2 * c.head)) = 2 * (a.move.apply c.head) := by
      cases a.move <;> simp only [Move.apply] <;> ring
    have htape : Function.update (Function.update (dtape M t) (2 * c.head) a.write)
        (a.move.apply (2 * c.head)) true = dtape M (t + 1) := by
      funext y
      obtain ⟨i, hi | hi⟩ := Int.even_or_odd' y
      · subst hi
        rw [Function.update_of_ne (by cases a.move <;> simp only [Move.apply] <;> omega),
          dtape_even]
        by_cases hip : i = c.head
        · subst hip
          rw [Function.update_self, hstepM]
          simp only
          rw [Function.update_self]
        · rw [Function.update_of_ne (by omega), dtape_even, hstepM]
          simp only
          rw [Function.update_of_ne hip]
      · subst hi
        by_cases hedge : (2 : ℤ) * i + 1 = a.move.apply (2 * c.head)
        · rw [dtape_odd, ← hedge, Function.update_self]
          symm
          rw [crossed_succ_iff]
          refine Or.inr ⟨by rw [hstepM, hnext]; simp, ?_⟩
          rw [hstepM]
          simp only
          cases hm : a.move
          · right
            rw [hm] at hedge
            simp only [Move.apply] at hedge ⊢
            constructor <;> omega
          · left
            rw [hm] at hedge
            simp only [Move.apply] at hedge ⊢
            constructor <;> omega
        · rw [Function.update_of_ne hedge, Function.update_of_ne (by omega), dtape_odd,
            dtape_odd]
          by_cases hcr : crossed M t i = true
          · rw [hcr]
            symm
            exact crossed_of_lt (by omega) hcr
          · simp only [Bool.not_eq_true] at hcr
            rw [hcr]
            symm
            simp only [Bool.eq_false_iff, ne_eq]
            intro hcon
            rcases (crossed_succ_iff M t i).1 hcon with h | ⟨-, h⟩
            · rw [hcr] at h; exact absurd h (by simp)
            · apply hedge
              rw [hstepM] at h
              simp only at h
              cases hm : a.move <;> rw [hm] at h <;> simp only [Move.apply] at h ⊢ <;> omega
    have h2 : 2 * (t + 1) = 2 * t + 1 + 1 := by ring
    rw [h2, run_succ, run_succ, hD, hs1, hs2, hhead, htape, hstepM]

/-! ### The final state -/

/-- Positions and ones of a blank-tape run are within `[-t, t]`. -/
theorem run_bound (M : Machine n) (t : ℕ) :
    (∀ p, (run M (init n) t).tape p = true → -(t : ℤ) ≤ p ∧ p ≤ t) ∧
      (-(t : ℤ) ≤ (run M (init n) t).head ∧ (run M (init n) t).head ≤ t) := by
  have h := ones_subset_run (M := M) (c := init n) (a := 0) (b := 0)
    (fun p hp => by simp [init, blank] at hp) (by simp [init]) t
  refine ⟨fun p hp => ?_, ?_⟩
  · have := h.1 p hp
    omega
  · have := h.2
    omega

theorem dtape_eq_false (M : Machine n) (t : ℕ) (y : ℤ) (hy : 2 * (t : ℤ) + 1 < y) :
    dtape M t y = false := by
  obtain ⟨i, hi | hi⟩ := Int.even_or_odd' y
  · subst hi
    rw [dtape_even]
    by_contra hcon
    simp only [Bool.not_eq_false] at hcon
    have := (run_bound M t).1 i hcon
    omega
  · subst hi
    rw [dtape_odd]
    by_contra hcon
    simp only [Bool.not_eq_false, crossed, decide_eq_true_eq] at hcon
    obtain ⟨s, hs, -, hcase⟩ := hcon
    have h1 := (run_bound M s).2
    rcases hcase with ⟨h2, -⟩ | ⟨h2, -⟩ <;> omega

/-- The final state runs right over the ones and appends one more. -/
theorem z_run (M : Machine n) (z : Fin n × Move) (c : ℤ) :
    ∀ (m : ℕ) (y : ℤ) (τ : ℤ → Bool), (c - y).toNat ≤ m → y ≤ c →
      (∀ p, c ≤ p → τ p = false) →
      ∃ (u : ℤ) (k : ℕ), y ≤ u ∧ τ u = false ∧
        (∀ p, y ≤ p → p < u → τ p = true) ∧
        run (double M z) ⟨some (bIdx n z), y, τ⟩ k = ⟨none, u + 1, Function.update τ u true⟩ := by
  intro m
  induction m with
  | zero =>
    intro y τ hm hy hc
    have hτ : τ y = false := hc y (by omega)
    refine ⟨y, 1, le_refl _, hτ, fun p h1 h2 => absurd h2 (by omega), ?_⟩
    show step (double M z) ⟨some (bIdx n z), y, τ⟩ = _
    unfold step
    simp only [double_card_z, hτ, Bool.false_eq_true, if_false]
    rfl
  | succ m ih =>
    intro y τ hm hy hc
    by_cases hτ : τ y = false
    · refine ⟨y, 1, le_refl _, hτ, fun p h1 h2 => absurd h2 (by omega), ?_⟩
      show step (double M z) ⟨some (bIdx n z), y, τ⟩ = _
      unfold step
      simp only [double_card_z, hτ, Bool.false_eq_true, if_false]
      rfl
    · simp only [Bool.not_eq_false] at hτ
      have hyc : y < c := by
        rcases lt_or_eq_of_le hy with h | h
        · exact h
        · exfalso
          rw [h, hc c (le_refl c)] at hτ
          exact absurd hτ (by simp)
      have hupd : Function.update τ y true = τ := by
        funext p
        by_cases hp : p = y
        · subst hp; rw [Function.update_self, hτ]
        · rw [Function.update_of_ne hp]
      have hstep : step (double M z) ⟨some (bIdx n z), y, τ⟩ = ⟨some (bIdx n z), y + 1, τ⟩ := by
        unfold step
        simp only [double_card_z, hτ, if_true]
        rw [hupd]
        rfl
      obtain ⟨u, k, h1, h2, h3, h4⟩ := ih (y + 1) τ (by omega) (by omega) hc
      refine ⟨u, 1 + k, by omega, h2, ?_, ?_⟩
      · intro p hp1 hp2
        rcases eq_or_lt_of_le hp1 with h | h
        · rw [← h]; exact hτ
        · exact h3 p (by omega) hp2
      · rw [run_add, run_succ, run_zero, hstep]
        exact h4

/-! ### The first visit to a square -/

/-- `M` scans the square `i` in an active state at some time. -/
def Visits (M : Machine n) (i : ℤ) : Prop :=
  ∃ s, (run M (init n) s).state ≠ none ∧ (run M (init n) s).head = i

/-- The first time at which `M` actively scans `i`. -/
noncomputable def firstVisit (M : Machine n) (i : ℤ) : ℕ :=
  if h : Visits M i then Nat.find h else 0

theorem firstVisit_spec {M : Machine n} {i : ℤ} (h : Visits M i) :
    (run M (init n) (firstVisit M i)).state ≠ none ∧
      (run M (init n) (firstVisit M i)).head = i := by
  unfold firstVisit
  rw [dif_pos h]
  exact Nat.find_spec h

theorem firstVisit_le {M : Machine n} {i : ℤ} (h : Visits M i) {s : ℕ}
    (hs : (run M (init n) s).state ≠ none ∧ (run M (init n) s).head = i) :
    firstVisit M i ≤ s := by
  unfold firstVisit
  rw [dif_pos h]
  exact Nat.find_min' h hs

/-- The edge crossed on the first visit to `i`. -/
noncomputable def edgeOf (M : Machine n) (i : ℤ) : ℤ :=
  min ((run M (init n) (firstVisit M i - 1)).head) i

/-- The first visit to a square other than the start arrives across an edge. -/
theorem firstVisit_prev {M : Machine n} {i : ℤ} (hi : i ≠ 0) (h : Visits M i) :
    1 ≤ firstVisit M i ∧ (run M (init n) (firstVisit M i - 1)).state ≠ none ∧
      ((run M (init n) (firstVisit M i - 1)).head = i - 1 ∨
        (run M (init n) (firstVisit M i - 1)).head = i + 1) := by
  obtain ⟨hst, hhd⟩ := firstVisit_spec h
  have h1 : 1 ≤ firstVisit M i := by
    rcases Nat.eq_zero_or_pos (firstVisit M i) with h0 | h0
    · exfalso
      rw [h0] at hhd
      exact hi (by simpa [init] using hhd.symm)
    · exact h0
  obtain ⟨s, hs⟩ : ∃ s, firstVisit M i = s + 1 := ⟨firstVisit M i - 1, by omega⟩
  have hact : (run M (init n) s).state ≠ none := by
    intro hnone
    rw [hs, run_succ, step_of_halted hnone, hnone] at hst
    exact hst rfl
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.1 hact
  have hstep : run M (init n) (s + 1)
      = ⟨(M.card q ((run M (init n) s).tape (run M (init n) s).head)).next,
          (M.card q ((run M (init n) s).tape (run M (init n) s).head)).move.apply
            (run M (init n) s).head,
          Function.update (run M (init n) s).tape (run M (init n) s).head
            (M.card q ((run M (init n) s).tape (run M (init n) s).head)).write⟩ := by
    rw [run_succ]
    unfold step
    rw [hq]
  refine ⟨h1, by rw [show firstVisit M i - 1 = s by omega]; exact hact, ?_⟩
  rw [show firstVisit M i - 1 = s by omega]
  have hhd' : (run M (init n) (s + 1)).head = i := by rw [← hs]; exact hhd
  rw [hstep] at hhd'
  simp only at hhd'
  cases hm : (M.card q ((run M (init n) s).tape (run M (init n) s).head)).move <;>
    rw [hm] at hhd' <;> simp only [Move.apply] at hhd' <;> omega

theorem edge_crossed {M : Machine n} {i : ℤ} (hi : i ≠ 0) (h : Visits M i) {t : ℕ}
    (ht : firstVisit M i ≤ t) : crossed M t (edgeOf M i) = true := by
  obtain ⟨h1, hact, hcase⟩ := firstVisit_prev hi h
  obtain ⟨hst, hhd⟩ := firstVisit_spec h
  obtain ⟨s, hs⟩ : ∃ s, firstVisit M i = s + 1 := ⟨firstVisit M i - 1, by omega⟩
  rw [hs] at hst hhd ht
  rw [show firstVisit M i - 1 = s by omega] at hact hcase
  simp only [crossed, decide_eq_true_eq]
  refine ⟨s, by omega, hst, ?_⟩
  unfold edgeOf
  rw [show firstVisit M i - 1 = s by omega]
  rcases hcase with hc | hc
  · left
    rw [hc, hhd]
    constructor
    · omega
    · omega
  · right
    rw [hc, hhd]
    constructor
    · omega
    · omega

theorem edgeOf_cases {M : Machine n} {i : ℤ} (hi : i ≠ 0) (h : Visits M i) :
    edgeOf M i = i - 1 ∨ edgeOf M i = i := by
  obtain ⟨-, -, hcase⟩ := firstVisit_prev hi h
  unfold edgeOf
  rcases hcase with hc | hc <;> rw [hc] <;> [left; right] <;> omega

theorem edgeOf_injOn {M : Machine n} {i j : ℤ} (hi : i ≠ 0) (hj : j ≠ 0)
    (hvi : Visits M i) (hvj : Visits M j) (h : edgeOf M i = edgeOf M j) : i = j := by
  by_contra hne
  obtain ⟨h1i, hacti, hcasei⟩ := firstVisit_prev hi hvi
  obtain ⟨h1j, hactj, hcasej⟩ := firstVisit_prev hj hvj
  have hprevi : firstVisit M ((run M (init n) (firstVisit M i - 1)).head) ≤ firstVisit M i - 1 :=
    firstVisit_le ⟨_, hacti, rfl⟩ ⟨hacti, rfl⟩
  have hprevj : firstVisit M ((run M (init n) (firstVisit M j - 1)).head) ≤ firstVisit M j - 1 :=
    firstVisit_le ⟨_, hactj, rfl⟩ ⟨hactj, rfl⟩
  have hei : edgeOf M i = min ((run M (init n) (firstVisit M i - 1)).head) i := rfl
  have hej : edgeOf M j = min ((run M (init n) (firstVisit M j - 1)).head) j := rfl
  rw [hei, hej] at h
  rcases hcasei with hci | hci <;> rcases hcasej with hcj | hcj <;>
    rw [hci] at h hprevi <;> rw [hcj] at h hprevj
  · rw [min_eq_left (by omega), min_eq_left (by omega)] at h
    omega
  · rw [min_eq_left (by omega), min_eq_right (by omega)] at h
    rw [h] at hprevi
    rw [show j + 1 = i by omega] at hprevj
    omega
  · rw [min_eq_right (by omega), min_eq_left (by omega)] at h
    rw [show i + 1 = j by omega] at hprevi
    rw [← h] at hprevj
    omega
  · rw [min_eq_right (by omega), min_eq_right (by omega)] at h
    omega

/-! ### The inequality (3) -/

/-- `SC(n)` is attained by some halting machine. -/
theorem exists_SC_witness (hn : 0 < n) : ∃ M : Machine n, Halts M ∧ scanCount M = SC n := by
  have hne : (Finset.univ.filter (fun M : Machine n => Halts M)).Nonempty := by
    refine ⟨⟨fun _ _ => ⟨false, .R, none⟩⟩, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨1, ?_⟩
    simp [run_succ, step, init, startState, dif_pos hn]
  obtain ⟨M, hM, hsup⟩ := Finset.exists_mem_eq_sup _ hne scanCount
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
  exact ⟨M, hM, by rw [SC, hsup]⟩

/-- A halting rule leaves a helper slot unused. -/
theorem exists_missing (M : Machine n)
    (h : ∃ (q : Fin n) (b : Bool), (M.card q b).next = none) :
    ∃ z : Fin n × Move, Missing M z := by
  classical
  obtain ⟨q0, b0, h0⟩ := h
  by_contra hcon
  push_neg at hcon
  set S : Finset (Fin n × Bool) := Finset.univ.filter (fun p => (M.card p.1 p.2).next ≠ none)
    with hS
  set f : Fin n × Bool → Fin n × Move :=
    fun p => ((M.card p.1 p.2).next.getD p.1, (M.card p.1 p.2).move) with hf
  have hsurj : (Finset.univ : Finset (Fin n × Move)) ⊆ S.image f := by
    intro w _
    obtain ⟨q, b, q', h1, h2⟩ : ∃ (q : Fin n) (b : Bool) (q' : Fin n),
        (M.card q b).next = some q' ∧ (q', (M.card q b).move) = w := by
      by_contra hc
      push_neg at hc
      exact hcon w (fun q b q' hq hw => hc q b q' hq hw)
    refine Finset.mem_image.2 ⟨(q, b), ?_, ?_⟩
    · simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, h1, ne_eq,
        reduceCtorEq, not_false_eq_true]
    · simp only [hf, h1, Option.getD_some]
      exact h2
  have hcard1 : (Finset.univ : Finset (Fin n × Move)).card ≤ S.card :=
    le_trans (Finset.card_le_card hsurj) Finset.card_image_le
  have hmem : (q0, b0) ∉ S := by simp [hS, h0]
  have hcard2 : S.card < (Finset.univ : Finset (Fin n × Bool)).card :=
    Finset.card_lt_card (Finset.ssubset_univ_iff.2 (fun hEq => hmem (hEq ▸ Finset.mem_univ _)))
  have hMove : Fintype.card Move = 2 := by decide
  have e1 : (Finset.univ : Finset (Fin n × Move)).card = n * 2 := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, hMove]
  have e2 : (Finset.univ : Finset (Fin n × Bool)).card = n * 2 := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  omega

/-- **The paper's (3)**: `SC(n) < Σ(3n)`. -/
theorem sc_lt_sigma (hn : 0 < n) : SC n < sigma (3 * n) := by
  classical
  obtain ⟨M, hM, hSC⟩ := exists_SC_witness hn
  have hex0 : HaltsInExactly M (haltTime M) := haltsInExactly_haltTime hM
  obtain ⟨T, hTeq⟩ : ∃ T, haltTime M = T + 1 := by
    refine ⟨haltTime M - 1, ?_⟩
    rcases Nat.eq_zero_or_pos (haltTime M) with h | h
    · exfalso
      have h1 := hex0.1
      rw [h] at h1
      simp [init, startState, dif_pos hn] at h1
    · omega
  have hex : HaltsInExactly M (T + 1) := by rw [← hTeq]; exact hex0
  obtain ⟨q, hq⟩ : ∃ q, (run M (init n) T).state = some q :=
    Option.ne_none_iff_exists'.1 (hex.2 T (by omega))
  set c := run M (init n) T with hc
  set a := M.card q (c.tape c.head) with ha
  have hstepM : run M (init n) (T + 1)
      = ⟨a.next, a.move.apply c.head, Function.update c.tape c.head a.write⟩ := by
    rw [run_succ, ← hc]
    unfold step
    rw [hq]
  have hnone : a.next = none := by
    have h1 := hex.1
    rw [hstepM] at h1
    exact h1
  obtain ⟨z, hz⟩ := exists_missing M ⟨q, c.tape c.head, hnone⟩
  have hsim := sim M hn hz T q hq
  have hstepD : run (double M z) (init (3 * n)) (2 * T + 1)
      = ⟨some (bIdx n z), a.move.apply (2 * c.head),
          Function.update (dtape M T) (2 * c.head) true⟩ := by
    rw [run_succ, hsim]
    unfold step
    simp only [← hc, dtape_even, ← ha, double_card_a, hnone]
  -- the final state appends a one
  have hhead : -(T : ℤ) ≤ c.head ∧ c.head ≤ (T : ℤ) := (run_bound M T).2
  set y := a.move.apply (2 * c.head) with hy
  set τ := Function.update (dtape M T) (2 * c.head) true with hτ
  have hbound : ∀ p, 2 * (T : ℤ) + 3 ≤ p → τ p = false := by
    intro p hp
    have hne : p ≠ 2 * c.head := by omega
    rw [hτ, Function.update_of_ne hne]
    exact dtape_eq_false M T p (by omega)
  have hyle : y ≤ 2 * (T : ℤ) + 3 := by
    rw [hy]
    cases a.move <;> simp only [Move.apply] <;> omega
  obtain ⟨u, k, hu1, hu2, -, hu4⟩ :=
    z_run M z (2 * (T : ℤ) + 3) ((2 * (T : ℤ) + 3 - y).toNat) y τ (le_refl _) hyle hbound
  have hfinal : run (double M z) (init (3 * n)) (2 * T + 1 + k)
      = ⟨none, u + 1, Function.update τ u true⟩ := by
    rw [run_add, hstepD]
    exact hu4
  -- the ones of the final tape
  set A := scanned M (T + 1) with hA
  have hAfin : A.Finite := scanned_finite M _
  have hAcard : A.ncard = SC n := by rw [hA, ← hSC, scanCount, hTeq]
  set φ : ℤ → ℤ := fun i => if i = 0 then 2 * c.head else 2 * edgeOf M i + 1 with hφ
  have hvisit : ∀ i ∈ A, Visits M i ∧ firstVisit M i ≤ T := by
    intro i hi
    obtain ⟨s, hs, h1, h2⟩ := hi
    exact ⟨⟨s, h1, h2⟩, le_trans (firstVisit_le ⟨s, h1, h2⟩ ⟨h1, h2⟩) (by omega)⟩
  have hτφ : ∀ i ∈ A, τ (φ i) = true := by
    intro i hi
    by_cases h0 : i = 0
    · simp only [hφ, h0, if_pos rfl]
      rw [hτ, Function.update_self]
    · simp only [hφ, if_neg h0]
      obtain ⟨hv, hfv⟩ := hvisit i hi
      rw [hτ, Function.update_of_ne (by omega), dtape_odd]
      exact edge_crossed h0 hv hfv
  have hinj : Set.InjOn φ A := by
    intro i hi j hj hij
    by_cases h0i : i = 0 <;> by_cases h0j : j = 0
    · rw [h0i, h0j]
    · exfalso
      simp only [hφ, h0i, if_pos rfl, if_neg h0j] at hij
      omega
    · exfalso
      simp only [hφ, h0j, if_pos rfl, if_neg h0i] at hij
      omega
    · simp only [hφ, if_neg h0i, if_neg h0j] at hij
      exact edgeOf_injOn h0i h0j (hvisit i hi).1 (hvisit j hj).1 (by omega)
  have hune : ∀ i ∈ A, φ i ≠ u := by
    intro i hi h
    rw [← h, hτφ i hi] at hu2
    exact absurd hu2 (by simp)
  have hsub : insert u (φ '' A) ⊆ ones (run (double M z) (init (3 * n)) (2 * T + 1 + k)) := by
    rw [hfinal]
    intro p hp
    rcases hp with rfl | ⟨i, hi, rfl⟩
    · show Function.update τ p true p = true
      rw [Function.update_self]
    · show Function.update τ u true (φ i) = true
      rw [Function.update_of_ne (hune i hi)]
      exact hτφ i hi
  have hfin : (ones (run (double M z) (init (3 * n)) (2 * T + 1 + k))).Finite := by
    apply Set.Finite.subset
      (Set.finite_Icc (0 - ((2 * T + 1 + k : ℕ) : ℤ)) (0 + ((2 * T + 1 + k : ℕ) : ℤ)))
    intro p hp
    have h := (ones_subset_run (M := double M z) (c := init (3 * n)) (a := 0) (b := 0)
      (fun p hp => by simp [init, blank] at hp) (by simp [init]) (2 * T + 1 + k)).1
    exact Set.mem_Icc.2 (h p hp)
  have hcount : SC n + 1 ≤ (ones (run (double M z) (init (3 * n)) (2 * T + 1 + k))).ncard := by
    have h1 : (insert u (φ '' A)).ncard = A.ncard + 1 := by
      rw [Set.ncard_insert_of_notMem (by rintro ⟨i, hi, hiu⟩; exact hune i hi hiu)
        (hAfin.image φ), Set.ncard_image_of_injOn hinj]
    calc SC n + 1 = A.ncard + 1 := by rw [hAcard]
      _ = (insert u (φ '' A)).ncard := h1.symm
      _ ≤ _ := Set.ncard_le_ncard hsub hfin
  have hscore : HaltsWithScore (double M z)
      ((ones (run (double M z) (init (3 * n)) (2 * T + 1 + k))).ncard) :=
    ⟨2 * T + 1 + k, by rw [hfinal], rfl⟩
  calc SC n < SC n + 1 := by omega
    _ ≤ _ := hcount
    _ ≤ sigma (3 * n) := le_sigma hscore

end Jones1974
