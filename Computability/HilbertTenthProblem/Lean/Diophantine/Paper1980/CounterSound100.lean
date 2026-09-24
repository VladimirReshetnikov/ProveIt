import Diophantine.Paper1980.CounterProgram100

/-!
# Serial runs of a compiled program are accepting computations

`EXPLORATION_THREE_RAW_COUNTER_UNIVERSAL_COMPILER.md`, §5: *"These local facts prove
inductively that the graph has exactly the logical counter computations, despite its
syntactic branch choices."*  And §6: *"Sections 4–6 decode that path into the fixed logical
counter execution."*

The run moves along lanes, so block `b` sits at lane `b mod 3`; it can stop only after the
halt's second bank, the one bank leading back to the entry.  Starting from the prefix, every
six blocks the run passes one logical instruction: at a boundary block `b₀` at the first lane
of an entry bank of location `ℓ` with physical values `2w`, the next six blocks are that
location's two banks, and they end at an entry bank of a successor with physical values
`2w'`, where `(ℓ, w) → (ℓ', w')` is a logical step.  The zero branch is legal only on a zero
register, because its first lane requests a zero test; the nonzero branch only on a positive
one, because its first bank decrements the physical value `2w_r`.  The halt's zero requests
force all three registers to zero.  Since the run is finite, it reaches the halt.
-/

namespace Jones1980

namespace CProgram

variable (M : CProgram) {x u : ℕ} {st val : ℕ → ℕ}

theorem run_lane (R : M.graph.SerialRun x u st val) : ∀ b, b < u → st b % 3 = b % 3 := by
  intro b
  induction b with
  | zero => intro _; rw [R.start]
  | succ b ih =>
    intro hb
    have hs : M.adj (st b) (st (b + 1)) = true := R.step b hb
    have h := M.adj_true hs
    have hb' := ih (by omega)
    by_cases h2 : st b % 3 = 2
    · have := (h.1 h2).1; omega
    · have := h.2 h2; omega

theorem run_cont (R : M.graph.SerialRun x u st val) {b : ℕ} (hb : b < u)
    (hne : ¬ (st b % 3 = 2 ∧ M.bankNext (st b / 3) 0 = true)) : b + 1 < u := by
  by_contra hc
  have hbu : b = u - 1 := by omega
  have hw : M.adj (st (u - 1)) 0 = true := R.wrap
  rw [← hbu] at hw
  have h := M.adj_true hw
  by_cases h2 : st b % 3 = 2
  · exact hne ⟨h2, by simpa using (h.1 h2).2⟩
  · have := h.2 h2; omega

/-- Along one pair of banks. -/
theorem run_bank (R : M.graph.SerialRun x u st val) {b0 s0 : ℕ} (hb0 : b0 < u)
    (hst : st b0 = 3 * s0) (hnext : ∀ t, M.bankNext s0 t = true → t = s0 + 1) :
    b0 + 5 < u ∧ ∀ j, j < 6 → st (b0 + j) = 3 * (s0 + j / 3) + j % 3 := by
  have hlane := M.run_lane R
  have hstep : ∀ b, b + 1 < u → st b % 3 ≠ 2 → st (b + 1) = st b + 1 := fun b hb h2 =>
    (M.adj_true (R.step b hb : M.adj (st b) (st (b + 1)) = true)).2 h2
  have h1 : b0 + 1 < u := M.run_cont R hb0 (fun h => by omega)
  have e1 : st (b0 + 1) = st b0 + 1 := hstep b0 h1 (by omega)
  have h2 : b0 + 2 < u := M.run_cont R h1 (fun h => by omega)
  have e2 : st (b0 + 2) = st (b0 + 1) + 1 := hstep (b0 + 1) h2 (by omega)
  have hdiv2 : st (b0 + 2) / 3 = s0 := by omega
  have h3 : b0 + 3 < u := M.run_cont R h2 (fun h => by
    rw [hdiv2] at h
    have := hnext 0 h.2
    omega)
  have hs3 : M.adj (st (b0 + 2)) (st (b0 + 3)) = true := R.step (b0 + 2) h3
  have hA := (M.adj_true hs3).1 (by omega)
  rw [hdiv2] at hA
  have e3 := hnext _ hA.2
  have hA3 := hA.1
  have h4 : b0 + 4 < u := M.run_cont R h3 (fun h => by omega)
  have e4 : st (b0 + 4) = st (b0 + 3) + 1 := hstep (b0 + 3) h4 (by omega)
  have h5 : b0 + 5 < u := M.run_cont R h4 (fun h => by omega)
  have e5 : st (b0 + 5) = st (b0 + 4) + 1 := hstep (b0 + 4) h5 (by omega)
  refine ⟨h5, fun j hj => ?_⟩
  interval_cases j <;> first | omega | (simp only [Nat.add_zero]; omega)

/-- The values across one pair of banks. -/
theorem run_bank_val (R : M.graph.SerialRun x u st val) {b0 s0 : ℕ} (h5 : b0 + 5 < u)
    (hst : ∀ j, j < 6 → st (b0 + j) = 3 * (s0 + j / 3) + j % 3) {i : ℕ} (hi : i < 3) :
    (val (b0 + 3 + i) : ℤ) = val (b0 + i) + (if M.sgnSL s0 i = true then 1 else -1) ∧
    (val (b0 + 6 + i) : ℤ) = val (b0 + 3 + i) + (if M.sgnSL (s0 + 1) i = true then 1 else -1) := by
  have u1 : (val (b0 + i + 3) : ℤ) = val (b0 + i)
      + (if M.sgnSL (st (b0 + i) / 3) (st (b0 + i) % 3) = true then 1 else -1) :=
    R.update (b0 + i) (by omega)
  have u2 : (val (b0 + (3 + i) + 3) : ℤ) = val (b0 + (3 + i))
      + (if M.sgnSL (st (b0 + (3 + i)) / 3) (st (b0 + (3 + i)) % 3) = true then 1 else -1) :=
    R.update (b0 + (3 + i)) (by omega)
  have a1 := hst i (by omega)
  have a2 := hst (3 + i) (by omega)
  rw [a1, show (3 * (s0 + i / 3) + i % 3) / 3 = s0 by omega,
    show (3 * (s0 + i / 3) + i % 3) % 3 = i by omega] at u1
  rw [a2, show (3 * (s0 + (3 + i) / 3) + (3 + i) % 3) / 3 = s0 + 1 by omega,
    show (3 * (s0 + (3 + i) / 3) + (3 + i) % 3) % 3 = i by omega] at u2
  rw [show b0 + i + 3 = b0 + 3 + i by omega] at u1
  rw [show b0 + (3 + i) + 3 = b0 + 6 + i by omega, show b0 + (3 + i) = b0 + 3 + i by omega] at u2
  exact ⟨u1, u2⟩

/-- A zero request is honoured. -/
theorem run_zero (R : M.graph.SerialRun x u st val) {b0 s0 : ℕ} (h5 : b0 + 5 < u)
    (hst : ∀ j, j < 6 → st (b0 + j) = 3 * (s0 + j / 3) + j % 3) {i : ℕ} (hi : i < 3)
    (hz : M.zeroSL s0 i = true) : val (b0 + i) = 0 := by
  apply R.zero_test (b0 + i) (by omega)
  show (!M.zeroSL (st (b0 + i) / 3) (st (b0 + i) % 3)) = false
  rw [hst i (by omega), show (3 * (s0 + i / 3) + i % 3) / 3 = s0 by omega,
    show (3 * (s0 + i / 3) + i % 3) % 3 = i by omega, hz]
  rfl

/-- Leaving a pair of banks that does not lead back to the entry. -/
theorem run_exit (R : M.graph.SerialRun x u st val) {b0 s1 : ℕ} (h5 : b0 + 5 < u)
    (hst5 : st (b0 + 5) = 3 * s1 + 2) (hno : M.bankNext s1 0 = false) :
    b0 + 6 < u ∧ st (b0 + 6) = 3 * (st (b0 + 6) / 3) ∧
      M.bankNext s1 (st (b0 + 6) / 3) = true := by
  have hd : st (b0 + 5) / 3 = s1 := by omega
  have h6 : b0 + 6 < u := M.run_cont R h5 (fun h => by rw [hd, hno] at h; simp at h)
  have hs6 : M.adj (st (b0 + 5)) (st (b0 + 6)) = true := R.step (b0 + 5) h6
  have hA := (M.adj_true hs6).1 (by omega)
  rw [hd] at hA
  exact ⟨h6, by omega, hA.2⟩

set_option maxHeartbeats 1000000 in
/-- **§§5–6.**  Every accepting serial run of the compiled graph on input `x` is an accepting
computation of the program on `x`. -/
theorem accepts_of_run (R : M.graph.SerialRun x u st val) : M.Accepts x := by
  have key : ∀ k, M.Accepts x ∨ ∃ ℓ w s,
      Relation.ReflTransGen M.Step (0, start x) (ℓ, w) ∧ 6 * k + 6 < u ∧
        st (6 * k + 6) = 3 * s ∧ M.entry ℓ s = true ∧
        ∀ i : Fin 3, val (6 * k + 6 + i) = 2 * w i := by
    intro k
    induction k with
    | zero =>
      right
      have hu := R.three_le
      obtain ⟨h5, hst⟩ := M.run_bank R (b0 := 0) (s0 := 0) (by omega) (by rw [R.start])
        (fun t h => by unfold bankNext at h; simpa using h)
      obtain ⟨h6, hst6, hent⟩ := M.run_exit R (b0 := 0) (s1 := 1) h5
        (by have := hst 5 (by norm_num); simpa using this)
        (by unfold bankNext; simp [M.entry_zero])
      unfold bankNext at hent
      simp only [zero_add, one_ne_zero, if_false, if_true] at hent
      refine ⟨0, start x, st 6 / 3, Relation.ReflTransGen.refl, h6, hst6, hent, fun i => ?_⟩
      have hv := M.run_bank_val R (b0 := 0) (s0 := 0) h5 hst i.isLt
      have hs0 : M.sgnSL 0 i = true := by unfold sgnSL; simp
      have hs1 : M.sgnSL (0 + 1) i = false := by unfold sgnSL; simp
      rw [hs0, hs1] at hv
      simp only [zero_add, if_true] at hv
      obtain ⟨h0, h1, h2⟩ := R.init
      fin_cases i <;> simp [start] at hv ⊢ <;> omega
    | succ k ih =>
      rcases ih with hacc | ⟨ℓ, w, s, hreach, hlt, hst0, hent, hval⟩
      · exact Or.inl hacc
      obtain ⟨hℓ, hcase⟩ := M.entry_true hent
      have hb6 : 6 * (k + 1) + 6 = 6 * k + 6 + 6 := by ring
      rw [hb6]
      rcases hcase with ⟨r, nx, hc, rfl⟩ | ⟨r, z, nz, hc, rfl | rfl⟩ | ⟨hc, rfl⟩
      -- an increment
      · right
        obtain ⟨h5, hst⟩ := M.run_bank R hlt hst0 (fun t h => by
          have e := M.bankNext_slot (ℓ := ℓ) (k := 0) (t := t) (by norm_num)
          simp only [Nat.add_zero] at e
          rw [e, hc] at h
          simpa using h)
        obtain ⟨h6, hst6, hnx⟩ := M.run_exit R (s1 := 2 + 4 * ℓ + 1) h5
          (by have := hst 5 (by norm_num); omega)
          (by rw [M.bankNext_slot (by norm_num), hc]; simp [M.entry_zero])
        rw [M.bankNext_slot (by norm_num), hc] at hnx
        simp only [Nat.one_ne_zero, beq_self_eq_true, Bool.true_and, Bool.false_and,
          Bool.false_or, beq_iff_eq] at hnx
        refine ⟨nx, Function.update w r (w r + 1), st (6 * k + 6 + 6) / 3,
          hreach.tail (Step.inc hℓ hc), h6, hst6, by simpa using hnx, fun i => ?_⟩
        have hv := M.run_bank_val R h5 hst i.isLt
        have e0 := M.sgnSL_slot (ℓ := ℓ) (k := 0) (l := i) (by norm_num); rw [hc] at e0
        have e1 := M.sgnSL_slot (ℓ := ℓ) (k := 1) (l := i) (by norm_num); rw [hc] at e1
        simp only [Nat.add_zero] at e0
        rw [show 2 + 4 * ℓ + 1 = 2 + 4 * ℓ + 1 from rfl, e0, e1] at hv
        have hw := hval i
        by_cases hir : i = r
        · subst hir
          simp at hv
          rw [Function.update_self]
          omega
        · have hne : (i : ℕ) ≠ (r : ℕ) := fun h => hir (Fin.ext h)
          simp [hne] at hv
          rw [Function.update_of_ne hir]
          omega
      -- the zero branch of a test
      · right
        obtain ⟨h5, hst⟩ := M.run_bank R hlt hst0 (fun t h => by
          have e := M.bankNext_slot (ℓ := ℓ) (k := 0) (t := t) (by norm_num)
          simp only [Nat.add_zero] at e
          rw [e, hc] at h
          simpa using h)
        have hz : M.zeroSL (2 + 4 * ℓ) r = true := by
          have e := M.zeroSL_slot (ℓ := ℓ) (k := 0) (l := r) (by norm_num)
          simp only [Nat.add_zero] at e
          rw [e, hc]
          simp
        have hr0 := M.run_zero R h5 hst r.isLt hz
        have hwr : w r = 0 := by have := hval r; omega
        obtain ⟨h6, hst6, hnx⟩ := M.run_exit R (s1 := 2 + 4 * ℓ + 1) h5
          (by have := hst 5 (by norm_num); omega)
          (by rw [M.bankNext_slot (by norm_num), hc]; simp [M.entry_zero])
        rw [M.bankNext_slot (by norm_num), hc] at hnx
        simp at hnx
        refine ⟨z, w, st (6 * k + 6 + 6) / 3, hreach.tail (Step.zero hℓ hc hwr), h6, hst6,
          hnx, fun i => ?_⟩
        have hv := M.run_bank_val R h5 hst i.isLt
        have e0 := M.sgnSL_slot (ℓ := ℓ) (k := 0) (l := i) (by norm_num); rw [hc] at e0
        have e1 := M.sgnSL_slot (ℓ := ℓ) (k := 1) (l := i) (by norm_num); rw [hc] at e1
        simp only [Nat.add_zero] at e0
        rw [e0, e1] at hv
        simp at hv
        have hw := hval i
        omega
      -- the nonzero branch of a test
      · right
        obtain ⟨h5, hst⟩ := M.run_bank R hlt hst0 (fun t h => by
          rw [M.bankNext_slot (by norm_num), hc] at h
          simpa using h)
        obtain ⟨h6, hst6, hnx⟩ := M.run_exit R (s1 := 2 + 4 * ℓ + 3) h5
          (by have := hst 5 (by norm_num); omega)
          (by rw [M.bankNext_slot (by norm_num), hc]; simp [M.entry_zero])
        rw [M.bankNext_slot (by norm_num), hc] at hnx
        simp at hnx
        have hvr := M.run_bank_val R h5 hst r.isLt
        have er := M.sgnSL_slot (ℓ := ℓ) (k := 2) (l := r) (by norm_num); rw [hc] at er
        rw [er] at hvr
        simp at hvr
        have hwr : w r ≠ 0 := by have := hval r; omega
        refine ⟨nz, Function.update w r (w r - 1), st (6 * k + 6 + 6) / 3,
          hreach.tail (Step.dec hℓ hc hwr), h6, hst6, hnx, fun i => ?_⟩
        have hv := M.run_bank_val R h5 hst i.isLt
        have e2 := M.sgnSL_slot (ℓ := ℓ) (k := 2) (l := i) (by norm_num); rw [hc] at e2
        have e3 := M.sgnSL_slot (ℓ := ℓ) (k := 3) (l := i) (by norm_num); rw [hc] at e3
        rw [show 2 + 4 * ℓ + 2 + 1 = 2 + 4 * ℓ + 3 by ring, e2, e3] at hv
        have hw := hval i
        by_cases hir : i = r
        · subst hir
          simp at hv
          rw [Function.update_self]
          omega
        · have hne : (i : ℕ) ≠ (r : ℕ) := fun h => hir (Fin.ext h)
          simp [hne] at hv
          rw [Function.update_of_ne hir]
          omega
      -- the accepting halt
      · left
        obtain ⟨h5, hst⟩ := M.run_bank R hlt hst0 (fun t h => by
          have e := M.bankNext_slot (ℓ := ℓ) (k := 0) (t := t) (by norm_num)
          simp only [Nat.add_zero] at e
          rw [e, hc] at h
          simpa using h)
        have hw0 : w = fun _ => 0 := by
          funext i
          have hz : M.zeroSL (2 + 4 * ℓ) i = true := by
            have e := M.zeroSL_slot (ℓ := ℓ) (k := 0) (l := i) (by norm_num)
            simp only [Nat.add_zero] at e
            rw [e, hc]
            simp
          have := M.run_zero R h5 hst i.isLt hz
          have := hval i
          omega
        exact ⟨ℓ, hℓ, hc, hw0 ▸ hreach⟩
  rcases key u with h | ⟨-, -, -, -, h, -⟩
  · exact h
  · omega

end CProgram

end Jones1980

namespace Jones1980

/-- The compiled graph meets the terminal convention: the only bank leading back to the entry
is the halt's second bank, which requests no zero test. -/
theorem CProgram.graph_conv (M : CProgram) :
    ∀ ii, ii < M.graph.n → M.graph.adj ii 0 = true → M.graph.zreq ii = true := by
  intro ii _ hadj
  have h := M.adj_true (hadj : M.adj ii 0 = true)
  by_cases h2 : ii % 3 = 2
  · obtain ⟨ℓ, hℓ, hc⟩ := M.bankNext_to_zero (by simpa using (h.1 h2).2)
    show (!M.zeroSL (ii / 3) (ii % 3)) = true
    rw [hℓ, M.zeroSL_slot (by norm_num), hc]
    rfl
  · have := h.2 h2; omega

/-- **The counter certificate decides program acceptance, in one direction.**  If a positive
solution of `Sys100` exists over the compiled ROM of a three-counter program, the program
accepts `x`. -/
theorem accepts_of_sys100 {M : CProgram}
    {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
    (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
    (hS : Sys100 (M.graph.rom M.graph.gridZon (3 ^ M.graph.sp)) x q J W H v t A0 A1 Kp Km D α
      R PC PV β z r a c d f h i j k o s w τ η ζ γ y) :
    M.Accepts x := by
  obtain ⟨_e, _m, _u, _hG, st, val, hrun⟩ := graph_serial_run100 M.graph_conv hP hS
  exact M.accepts_of_run hrun

end Jones1980
