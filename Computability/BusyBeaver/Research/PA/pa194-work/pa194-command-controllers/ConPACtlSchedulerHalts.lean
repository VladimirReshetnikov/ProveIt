import ConPACtlScheduler

/-!
# A derivation of contradiction makes the scheduler halt

* `drain`: a continuation pointer strictly decreases, so the scheduler returns to an empty
  continuation without changing its candidate;
* `reach`: from an empty continuation it reaches every later candidate;
* `final_word_halts`: the word `AX 0 0 0; DISCARD; W; SHIFT` halts from every store when `W`
  computes the formula `1`;
* `derivation_halts`: if `G S 1`, every run from `⟪2, 0, σ⟫` meets a halting SHIFT.

All of this holds in an arbitrary model of `𝗜𝚺₁`, with words, candidates and times that may
be nonstandard.
-/
set_option autoImplicit false
noncomputable section
namespace ConPA.Ctl
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor (cantor first second triangle)

section model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {S : Sem V} (R : Run V S)

lemma second_le (p : V) : second p ≤ p :=
  (SetTheory.BusyBeaver.ZFC.ArithmeticCantor.projections_spec p).2.1

lemma nextL_le (s : V) : nextL s ≤ s := by
  unfold nextL
  split_ifs
  · exact second_le s
  · exact le_trans (second_le _) (second_le s)
  · exact le_trans (second_le _) (le_trans (second_le _) (second_le s))

/-- The scheduler returns to an empty continuation with the same candidate. -/
lemma drain (x : V) : ∃ k, π₁ (R.run k x) = π₁ x ∧ π₁ (π₂ (R.run k x)) = 0 := by
  have hP : ∀ j : V, (∃ i ≤ j, π₁ (π₂ (R.run i x)) = 0 ∧ π₁ (R.run i x) = π₁ x) ∨
      (π₁ (π₂ (R.run j x)) + j ≤ π₁ (π₂ x) ∧ π₁ (R.run j x) = π₁ x) := by
    intro j
    induction j using ISigma1.sigma1_succ_induction
    · definability
    case zero => right; simp [R.run_zero]
    case succ j ih =>
      rcases ih with (⟨i, hi, h⟩ | ⟨hl, hn⟩)
      · exact Or.inl ⟨i, le_trans hi (by simp), h⟩
      · by_cases h0 : π₁ (π₂ (R.run j x)) = 0
        · exact Or.inl ⟨j, by simp, h0, hn⟩
        · right
          rw [R.run_succ, state_eta3 (R.run j x), sstep_mk]
          simp only [pi₁_pair, pi₂_pair, if_neg h0]
          refine ⟨?_, hn⟩
          have hs : seed (π₁ (R.run j x)) (π₁ (π₂ (R.run j x))) = π₁ (π₂ (R.run j x)) - 1 := by
            simp [seed, h0]
          have h1 : nextL (seed (π₁ (R.run j x)) (π₁ (π₂ (R.run j x)))) + 1 ≤
              π₁ (π₂ (R.run j x)) := by
            rw [hs]
            calc nextL (π₁ (π₂ (R.run j x)) - 1) + 1 ≤ (π₁ (π₂ (R.run j x)) - 1) + 1 :=
                  add_le_add_left (nextL_le _) 1
              _ = π₁ (π₂ (R.run j x)) :=
                  sub_add_self_of_le (pos_iff_one_le.mp (pos_iff_ne_zero.mpr h0))
          calc nextL (seed (π₁ (R.run j x)) (π₁ (π₂ (R.run j x)))) + (j + 1)
              = nextL (seed (π₁ (R.run j x)) (π₁ (π₂ (R.run j x)))) + 1 + j := by ring
            _ ≤ π₁ (π₂ (R.run j x)) + j := add_le_add_left h1 j
            _ ≤ π₁ (π₂ x) := hl
  rcases hP (π₁ (π₂ x) + 1) with (⟨i, _, h0, hn⟩ | ⟨hl, _⟩)
  · exact ⟨i, hn, h0⟩
  · exfalso
    have h2 : π₁ (π₂ x) + 1 ≤ π₁ (π₂ x) := le_trans (le_add_of_nonneg_left (by simp)) hl
    exact absurd h2 (not_le.mpr (by simp))

/-- From an empty continuation the scheduler reaches every later candidate. -/
lemma reach (x₀ : V) (h0 : π₁ (π₂ x₀) = 0) (m : V) :
    ∃ k, π₁ (R.run k x₀) = π₁ x₀ + m ∧ π₁ (π₂ (R.run k x₀)) = 0 := by
  induction m using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨0, by simp [R.run_zero], by simpa [R.run_zero] using h0⟩
  case succ m ih =>
    obtain ⟨k, hn, hl⟩ := ih
    obtain ⟨i, hin, hil⟩ := drain R (R.run (k + 1) x₀)
    refine ⟨k + 1 + i, ?_, ?_⟩
    · rw [R.run_add, hin, R.run_succ, state_eta3 (R.run k x₀), sstep_mk]
      simp [hl, hn, add_assoc]
    · rw [R.run_add]
      exact hil

variable (S) in
lemma tail_halts {W : V} (hW : Good S W 1) (v δ : V) :
    flg(tstep S SH (texec S W ⟪⟪0, v, 0, 0⟫, δ, 0⟫)) = 1 := by
  rcases good_run S hW v δ with (hh | he)
  · rw [tstep_of_flag S SH _ (by rw [hh]; simp)]
    exact hh
  · rw [he, tstep_SH_halt S 1 0 v 0 δ (by simp)]
    simp

variable (S) in
/-- Reset by an AX, clear the top, compute `1`, test it. -/
lemma final_word_halts {W : V} (hW : Good S W 1) (σ : V) :
    flg(texec S (snoc ((snoc 0 (AX 0 0 0) ⧺ DISCARD) ⧺ W) SH) ⟪σ, 0, 0⟫) = 1 := by
  obtain ⟨t, w, d, h, rfl⟩ : ∃ t w d h : V, σ = ⟪t, w, d, h⟫ :=
    ⟨π₁ σ, π₁ (π₂ σ), π₁ (π₂ (π₂ σ)), π₂ (π₂ (π₂ σ)), by simp⟩
  rw [texec_snoc, texec_seqApp, texec_seqApp, texec_snoc, texec_nil, tstep_AX, discard_run]
  exact tail_halts S hW _ _

/-- **If some word computes the formula `1`, the scheduler halts.** -/
theorem derivation_halts (σ : V) (h1 : G S 1) : ∃ k, shalt (R.run k ⟪2, 0, σ⟫) := by
  obtain ⟨W, hW⟩ := h1
  obtain ⟨Wf, hWf⟩ : ∃ Wf : V, Wf = snoc ((snoc 0 (AX 0 0 0) ⧺ DISCARD) ⧺ W) SH := ⟨_, rfl⟩
  have hc3 : (3 : V) ≤ ptr Wf 3 (len Wf) := le_ptr Wf 3 (len Wf)
  obtain ⟨m, hm⟩ : ∃ m : V, ptr Wf 3 (len Wf) = m + 3 :=
    ⟨ptr Wf 3 (len Wf) - 3, (sub_add_self_of_le hc3).symm⟩
  obtain ⟨k, hn, hl⟩ := reach R ⟪2, 0, σ⟫ (by simp) m
  have hpt : PtIs (R.run k ⟪2, 0, σ⟫) (ptr Wf 3 (len Wf)) :=
    Or.inl ⟨hl, by rw [hn, hm, pi₁_pair]; ring⟩
  have hfin : flg(texec S Wf ⟪π₂ (π₂ (R.run k ⟪2, 0, σ⟫)), 0, 0⟫) = 1 := by
    rw [hWf]
    exact final_word_halts S hW _
  obtain ⟨j, hj⟩ := word_halts R Wf 3 _ _ (by norm_num) hpt rfl hfin
  exact ⟨k + j, by rw [R.run_add]; exact hj⟩

end model

#print axioms run_inv
#print axioms word_halts
#print axioms reach
#print axioms derivation_halts
end ConPA.Ctl
