import Diophantine.Paper1980.CounterIff100

/-!
# Counter-program macros

`EXPLORATION_THREE_RAW_COUNTER_UNIVERSAL_COMPILER.md`, §1: *"For any fixed integer b>=2 and
digit d in {1,...,b-1}, a push on A implements A:=bA+d while preserving B and finishing with
C=0 ...  A pop on A computes the quotient floor(A/b) in A and returns the remainder in finite
control, again preserving B and restoring C=0."*

The macros are instruction blocks given as functions from offsets to instructions, placed at a
base location with absolute exits.  Each comes with its specification as reachability in the
logical step relation:

* `transferM r s`: `s += r`, `r := 0`;
* `mulTransferM r s k`: `s += k r`, `r := 0`;
* `incsM r d`: `r += d`;
* `pushM r c k d`: with `c = 0`, `r := k r + d`;
* `popM r c k`: with `c = 0`, `r := r / k`, exiting at the exit of the remainder `r mod k`.

`CProgram.next` is the step relation as a partial function; the relation is deterministic.
-/

namespace Jones1980

namespace CProgram

variable (M : CProgram)

/-- The logical step as a partial function. -/
def next : ℕ × (Fin 3 → ℕ) → Option (ℕ × (Fin 3 → ℕ))
  | (ℓ, v) =>
    if ℓ < M.len then
      match M.code ℓ with
      | .inc r nx => some (nx, Function.update v r (v r + 1))
      | .test r z nz => if v r = 0 then some (z, v) else some (nz, Function.update v r (v r - 1))
      | .accept => none
      | .stop => none
    else none

theorem step_iff_next {a b : ℕ × (Fin 3 → ℕ)} : M.Step a b ↔ M.next a = some b := by
  obtain ⟨ℓ, v⟩ := a
  constructor
  · intro h
    cases h with
    | inc hℓ hc => simp [next, hℓ, hc]
    | zero hℓ hc hv => simp [next, hℓ, hc, hv]
    | dec hℓ hc hv => simp [next, hℓ, hc, hv]
  · intro h
    by_cases hℓ : ℓ < M.len
    · cases hc : M.code ℓ with
      | inc r nx =>
        simp only [next, hℓ, if_true, hc, Option.some.injEq] at h
        rw [← h]; exact Step.inc hℓ hc
      | test r z nz =>
        by_cases hv : v r = 0
        · simp only [next, hℓ, if_true, hc, hv, Option.some.injEq] at h
          rw [← h]; exact Step.zero hℓ hc hv
        · simp only [next, hℓ, if_true, hc, hv, if_false, Option.some.injEq] at h
          rw [← h]; exact Step.dec hℓ hc hv
      | accept => simp [next, hℓ, hc] at h
      | stop => simp [next, hℓ, hc] at h
    · simp [next, hℓ] at h

/-- A block of instructions sits at a base location. -/
def Placed (ℓ size : ℕ) (f : ℕ → CInstr) : Prop :=
  ∀ o, o < size → ℓ + o < M.len ∧ M.code (ℓ + o) = f o

abbrev Reach (a b : ℕ × (Fin 3 → ℕ)) : Prop := Relation.ReflTransGen M.Step a b

theorem Placed.get {ℓ size : ℕ} {f : ℕ → CInstr} (h : M.Placed ℓ size f) {o : ℕ}
    (ho : o < size) : ℓ + o < M.len ∧ M.code (ℓ + o) = f o := h o ho

/-! ### Transfer -/

/-- `s += r`, `r := 0`. -/
def transferM (r s : Fin 3) (ℓ exit : ℕ) : ℕ → CInstr := fun o =>
  if o = 0 then .test r exit (ℓ + 1) else .inc s ℓ

theorem transfer_spec {r s : Fin 3} (hrs : r ≠ s) {ℓ exit : ℕ}
    (hP : M.Placed ℓ 2 (transferM r s ℓ exit)) :
    ∀ (n : ℕ) (v : Fin 3 → ℕ), v r = n →
      M.Reach (ℓ, v) (exit, Function.update (Function.update v s (v s + v r)) r 0) := by
  have h0 := hP.get M (o := 0) (by norm_num)
  have h1 := hP.get M (o := 1) (by norm_num)
  simp only [Nat.add_zero, transferM, if_true, one_ne_zero, if_false] at h0 h1
  intro n
  induction n with
  | zero =>
    intro v hv
    have e : Function.update (Function.update v s (v s + v r)) r 0 = v := by
      funext i
      simp only [Function.update_apply]
      split_ifs with h1 h2 <;> subst_vars <;> omega
    rw [e]
    exact Relation.ReflTransGen.single (Step.zero h0.1 h0.2 hv)
  | succ n ih =>
    intro v hv
    have s1 : M.Step (ℓ, v) (ℓ + 1, Function.update v r (v r - 1)) :=
      Step.dec h0.1 h0.2 (by omega)
    set v1 := Function.update v r (v r - 1) with hv1
    have s2 : M.Step (ℓ + 1, v1) (ℓ, Function.update v1 s (v1 s + 1)) := Step.inc h1.1 h1.2
    set v2 := Function.update v1 s (v1 s + 1) with hv2
    have hv2r : v2 r = n := by
      rw [hv2, hv1, Function.update_of_ne hrs.symm.symm, Function.update_self]
      · omega
    have hrest := ih v2 hv2r
    have e : Function.update (Function.update v2 s (v2 s + v2 r)) r 0
        = Function.update (Function.update v s (v s + v r)) r 0 := by
      funext i
      simp only [hv2, hv1, Function.update_apply]
      split_ifs <;> subst_vars <;> first | omega | (exfalso; exact hrs rfl)
    rw [e] at hrest
    exact (Relation.ReflTransGen.single s1).trans ((Relation.ReflTransGen.single s2).trans hrest)

/-- The transfer, in property form. -/
theorem transfer_spec' {r s : Fin 3} (hrs : r ≠ s) {ℓ exit : ℕ}
    (hP : M.Placed ℓ 2 (transferM r s ℓ exit)) (v : Fin 3 → ℕ) :
    ∃ w, M.Reach (ℓ, v) (exit, w) ∧ w r = 0 ∧ w s = v s + v r ∧
      ∀ i, i ≠ r → i ≠ s → w i = v i := by
  refine ⟨_, M.transfer_spec hrs hP (v r) v rfl, by simp, ?_, fun i hr hs => ?_⟩
  · rw [Function.update_of_ne hrs.symm, Function.update_self]
  · rw [Function.update_of_ne hr, Function.update_of_ne hs]

/-! ### Increments -/

/-- `d` increments of `s`, `d ≥ 1`. -/
def incsM (s : Fin 3) (d ℓ exit : ℕ) : ℕ → CInstr := fun o =>
  .inc s (if o + 1 < d then ℓ + o + 1 else exit)

theorem incs_spec {s : Fin 3} {d ℓ exit : ℕ} (hd : 1 ≤ d) (hP : M.Placed ℓ d (incsM s d ℓ exit))
    (v : Fin 3 → ℕ) :
    ∃ w, M.Reach (ℓ, v) (exit, w) ∧ w s = v s + d ∧ ∀ i, i ≠ s → w i = v i := by
  -- from offset `j`, the remaining `d − j` increments
  have key : ∀ t, ∀ j (v : Fin 3 → ℕ), j + t + 1 = d →
      ∃ w, M.Reach (ℓ + j, v) (exit, w) ∧ w s = v s + (t + 1) ∧ ∀ i, i ≠ s → w i = v i := by
    intro t
    induction t with
    | zero =>
      intro j v hj
      have h := hP.get M (o := j) (by omega)
      simp only [incsM, if_neg (show ¬ (j + 1 < d) by omega)] at h
      refine ⟨_, Relation.ReflTransGen.single (Step.inc h.1 h.2), by simp, fun i hi => ?_⟩
      rw [Function.update_of_ne hi]
    | succ t ih =>
      intro j v hj
      have h := hP.get M (o := j) (by omega)
      simp only [incsM, if_pos (show j + 1 < d by omega)] at h
      obtain ⟨w, hw, hws, hwi⟩ := ih (j + 1) (Function.update v s (v s + 1)) (by omega)
      refine ⟨w, (Relation.ReflTransGen.single (Step.inc h.1 h.2)).trans ?_, ?_, fun i hi => ?_⟩
      · rw [show ℓ + (j + 1) = ℓ + j + 1 by ring] at hw; exact hw
      · rw [hws, Function.update_self]; ring
      · rw [hwi i hi, Function.update_of_ne hi]
  obtain ⟨w, hw, h1, h2⟩ := key (d - 1) 0 v (by omega)
  rw [Nat.add_zero] at hw
  exact ⟨w, hw, by rw [h1]; congr 1; omega, h2⟩

/-! ### Multiplying transfer -/

/-- `s += k r`, `r := 0`, `k ≥ 1`. -/
def mulTransferM (r s : Fin 3) (k ℓ exit : ℕ) : ℕ → CInstr := fun o =>
  if o = 0 then .test r exit (ℓ + 1) else incsM s k (ℓ + 1) ℓ (o - 1)

theorem mulTransfer_spec {r s : Fin 3} (hrs : r ≠ s) {k ℓ exit : ℕ} (hk : 1 ≤ k)
    (hP : M.Placed ℓ (k + 1) (mulTransferM r s k ℓ exit)) :
    ∀ (n : ℕ) (v : Fin 3 → ℕ), v r = n →
      ∃ w, M.Reach (ℓ, v) (exit, w) ∧ w r = 0 ∧ w s = v s + k * n ∧
        ∀ i, i ≠ r → i ≠ s → w i = v i := by
  have h0 := hP.get M (o := 0) (by omega)
  simp only [Nat.add_zero, mulTransferM, if_true] at h0
  have hI : M.Placed (ℓ + 1) k (incsM s k (ℓ + 1) ℓ) := fun o ho => by
    have h := hP.get M (o := o + 1) (by omega)
    simp only [mulTransferM, if_neg (show o + 1 ≠ 0 by omega), Nat.add_sub_cancel] at h
    rw [show ℓ + 1 + o = ℓ + (o + 1) by ring]
    exact h
  intro n
  induction n with
  | zero =>
    intro v hv
    exact ⟨v, Relation.ReflTransGen.single (Step.zero h0.1 h0.2 hv), hv, by ring,
      fun i _ _ => rfl⟩
  | succ n ih =>
    intro v hv
    have s1 : M.Step (ℓ, v) (ℓ + 1, Function.update v r (v r - 1)) :=
      Step.dec h0.1 h0.2 (by omega)
    obtain ⟨w1, hw1, hw1s, hw1i⟩ := M.incs_spec hk hI (Function.update v r (v r - 1))
    have hw1r : w1 r = n := by rw [hw1i r hrs, Function.update_self]; omega
    obtain ⟨w, hw, hwr, hws, hwi⟩ := ih w1 hw1r
    refine ⟨w, (Relation.ReflTransGen.single s1).trans (hw1.trans hw), hwr, ?_, fun i hr hs => ?_⟩
    · rw [hws, hw1s, Function.update_of_ne hrs.symm]; ring
    · rw [hwi i hr hs, hw1i i hs, Function.update_of_ne hr]

/-! ### Push -/

/-- `r := k r + d` using the scratch `c = 0`; `k, d ≥ 1`. -/
def pushM (r c : Fin 3) (k d ℓ exit : ℕ) : ℕ → CInstr := fun o =>
  if o < k + 1 then mulTransferM r c k ℓ (ℓ + k + 1) o
  else if o < k + 3 then transferM c r (ℓ + k + 1) (ℓ + k + 3) (o - (k + 1))
  else incsM r d (ℓ + k + 3) exit (o - (k + 3))

theorem push_spec {r c : Fin 3} (hrc : r ≠ c) {k d ℓ exit : ℕ} (hk : 1 ≤ k) (hd : 1 ≤ d)
    (hP : M.Placed ℓ (k + 3 + d) (pushM r c k d ℓ exit)) (v : Fin 3 → ℕ) (hc : v c = 0) :
    ∃ w, M.Reach (ℓ, v) (exit, w) ∧ w r = k * v r + d ∧ w c = 0 ∧
      ∀ i, i ≠ r → i ≠ c → w i = v i := by
  have hP1 : M.Placed ℓ (k + 1) (mulTransferM r c k ℓ (ℓ + k + 1)) := fun o ho => by
    have h := hP.get M (o := o) (by omega)
    simp only [pushM, if_pos ho] at h
    exact h
  have hP2 : M.Placed (ℓ + k + 1) 2 (transferM c r (ℓ + k + 1) (ℓ + k + 3)) := fun o ho => by
    have h := hP.get M (o := k + 1 + o) (by omega)
    simp only [pushM, if_neg (show ¬ (k + 1 + o < k + 1) by omega),
      if_pos (show k + 1 + o < k + 3 by omega), show k + 1 + o - (k + 1) = o by omega] at h
    rw [show ℓ + k + 1 + o = ℓ + (k + 1 + o) by ring]
    exact h
  have hP3 : M.Placed (ℓ + k + 3) d (incsM r d (ℓ + k + 3) exit) := fun o ho => by
    have h := hP.get M (o := k + 3 + o) (by omega)
    simp only [pushM, if_neg (show ¬ (k + 3 + o < k + 1) by omega),
      if_neg (show ¬ (k + 3 + o < k + 3) by omega), show k + 3 + o - (k + 3) = o by omega] at h
    rw [show ℓ + k + 3 + o = ℓ + (k + 3 + o) by ring]
    exact h
  obtain ⟨w1, h1, h1r, h1c, h1i⟩ := M.mulTransfer_spec hrc hk hP1 (v r) v rfl
  obtain ⟨w2, h2, h2c, h2r, h2i⟩ := M.transfer_spec' hrc.symm hP2 w1
  obtain ⟨w3, h3, h3r, h3i⟩ := M.incs_spec hd hP3 w2
  refine ⟨w3, h1.trans (h2.trans h3), ?_, ?_, fun i hr hc' => ?_⟩
  · rw [h3r, h2r, h1r, h1c, hc]; ring
  · rw [h3i c hrc.symm, h2c]
  · rw [h3i i hr, h2i i hc' hr, h1i i hr hc']

/-! ### Pop -/

/-- `r := r / k` using the scratch `c = 0`, exiting by the remainder; `k ≥ 1`. -/
def popM (r c : Fin 3) (k ℓ : ℕ) (exits : ℕ → ℕ) : ℕ → CInstr := fun o =>
  if o < k then .test r (ℓ + k + 1 + 2 * o) (if o + 1 < k then ℓ + o + 1 else ℓ + k)
  else if o = k then .inc c ℓ
  else transferM c r (ℓ + k + 1 + 2 * ((o - (k + 1)) / 2)) (exits ((o - (k + 1)) / 2))
    ((o - (k + 1)) % 2)

theorem pop_spec {r c : Fin 3} (hrc : r ≠ c) {k ℓ : ℕ} {exits : ℕ → ℕ} (hk : 1 ≤ k)
    (hP : M.Placed ℓ (3 * k + 1) (popM r c k ℓ exits)) (v : Fin 3 → ℕ) (hc : v c = 0) :
    ∃ w, M.Reach (ℓ, v) (exits (v r % k), w) ∧ w r = v r / k ∧ w c = 0 ∧
      ∀ i, i ≠ r → i ≠ c → w i = v i := by
  -- the exit transfers
  have hT : ∀ j, j < k → M.Placed (ℓ + k + 1 + 2 * j) 2
      (transferM c r (ℓ + k + 1 + 2 * j) (exits j)) := fun j hj o ho => by
    have h := hP.get M (o := k + 1 + 2 * j + o) (by omega)
    simp only [popM, if_neg (show ¬ (k + 1 + 2 * j + o < k) by omega),
      if_neg (show k + 1 + 2 * j + o ≠ k by omega),
      show (k + 1 + 2 * j + o - (k + 1)) / 2 = j by omega,
      show (k + 1 + 2 * j + o - (k + 1)) % 2 = o by omega] at h
    rw [show ℓ + k + 1 + 2 * j + o = ℓ + (k + 1 + 2 * j + o) by ring]
    exact h
  have hk' := hP.get M (o := k) (by omega)
  simp only [popM, lt_irrefl, if_false, if_true] at hk'
  -- the division loop
  have loop : ∀ n, ∀ j (u : Fin 3 → ℕ), j < k → u r = n →
      M.Reach (ℓ + j, u) (ℓ + k + 1 + 2 * ((j + n) % k),
        Function.update (Function.update u c (u c + (j + n) / k)) r 0) := by
    intro n
    induction n with
    | zero =>
      intro j u hj hu
      have h := hP.get M (o := j) (by omega)
      simp only [popM, if_pos hj] at h
      have e : Function.update (Function.update u c (u c + (j + 0) / k)) r 0 = u := by
        funext i
        rw [show (j + 0) / k = 0 by rw [Nat.add_zero]; exact Nat.div_eq_of_lt hj]
        simp only [Nat.add_zero, Function.update_apply]
        split_ifs <;> subst_vars <;> omega
      rw [e, show (j + 0) % k = j by rw [Nat.add_zero]; exact Nat.mod_eq_of_lt hj]
      exact Relation.ReflTransGen.single (Step.zero h.1 h.2 hu)
    | succ n ih =>
      intro j u hj hu
      have h := hP.get M (o := j) (by omega)
      simp only [popM, if_pos hj] at h
      have s1 := Step.dec h.1 h.2 (show u r ≠ 0 by omega)
      set u1 := Function.update u r (u r - 1) with hu1
      have hu1r : u1 r = n := by rw [hu1, Function.update_self]; omega
      by_cases hjk : j + 1 < k
      · rw [if_pos hjk] at s1
        have hrest := ih (j + 1) u1 hjk hu1r
        rw [show ℓ + (j + 1) = ℓ + j + 1 by ring, show j + 1 + n = j + (n + 1) by ring] at hrest
        have e : Function.update (Function.update u1 c (u1 c + (j + (n + 1)) / k)) r 0
            = Function.update (Function.update u c (u c + (j + (n + 1)) / k)) r 0 := by
          funext i
          simp only [hu1, Function.update_apply]
          split_ifs <;> subst_vars <;> first | omega | (exfalso; exact hrc rfl)
        rw [e] at hrest
        exact (Relation.ReflTransGen.single s1).trans hrest
      · rw [if_neg hjk] at s1
        have hj1 : j = k - 1 := by omega
        have s2 : M.Step (ℓ + k, u1) (ℓ, Function.update u1 c (u1 c + 1)) := Step.inc hk'.1 hk'.2
        set u2 := Function.update u1 c (u1 c + 1) with hu2
        have hu2r : u2 r = n := by rw [hu2, Function.update_of_ne hrc]; exact hu1r
        have hrest := ih 0 u2 (by omega) hu2r
        rw [Nat.add_zero, Nat.zero_add] at hrest
        have hmod : (j + (n + 1)) % k = n % k := by
          rw [hj1, show k - 1 + (n + 1) = n + k by omega, Nat.add_mod_right]
        have hdiv : (j + (n + 1)) / k = n / k + 1 := by
          rw [hj1, show k - 1 + (n + 1) = n + k * 1 by omega, Nat.add_mul_div_left _ _ (by omega)]
        rw [hmod, hdiv]
        have e : Function.update (Function.update u2 c (u2 c + n / k)) r 0
            = Function.update (Function.update u c (u c + (n / k + 1))) r 0 := by
          funext i
          simp only [hu2, hu1, Function.update_apply]
          split_ifs <;> subst_vars <;> first | omega | (exfalso; exact hrc rfl)
        rw [e] at hrest
        exact (Relation.ReflTransGen.single s1).trans ((Relation.ReflTransGen.single s2).trans hrest)
  have hl := loop (v r) 0 v (by omega) rfl
  rw [Nat.add_zero, Nat.zero_add] at hl
  set u := Function.update (Function.update v c (v c + v r / k)) r 0 with hu
  obtain ⟨w, hw, hwc, hwr, hwi⟩ := M.transfer_spec' hrc.symm
    (hT (v r % k) (Nat.mod_lt _ (by omega))) u
  refine ⟨w, hl.trans hw, ?_, hwc, fun i hr hc' => ?_⟩
  · rw [hwr, hu, Function.update_self, Function.update_of_ne hrc.symm, Function.update_self, hc]
    ring
  · rw [hwi i hc' hr, hu, Function.update_of_ne hr, Function.update_of_ne hc']


end CProgram

end Jones1980
