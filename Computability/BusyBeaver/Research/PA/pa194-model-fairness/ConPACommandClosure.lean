import ConPACommandGadgets
import Mathlib.Tactic.IntervalCases

/-!
# Formulas computed by command words

`G S r` (some word leaves `r` on top of the empty stack, or halts) is closed under the rules
of the separate-diagonal numerical calculus as the commands implement them:

* `G_leaf`: each of the eight leaf formulas of an AX, for all parameters with `d ≤ D`;
* `G_axT`: the top formula of an AX (the guarded gate);
* `G_gen`: from `a` to its generalization `4 * cantor a i + 2`;
* `G_mp`: from `a` and the implication `4 * cantor a b` to `b`.

The words are those of `pa194-derivation-compiler`. The proofs run them in an arbitrary model
of `𝗜𝚺₁`; the frame property `good_run` supplies the induction hypotheses on the nonempty
stacks that the modus ponens word creates.
-/
set_option autoImplicit false
noncomputable section
namespace ConPA.Words
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor (cantor first second triangle)

section model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (S : Sem V)

/-- Composition of runs that may halt. -/
lemma chain {W U τ σ σ' : V} (h : flg(texec S W τ) = 1 ∨ texec S W τ = σ)
    (hU : flg(texec S U σ) = 1 ∨ texec S U σ = σ') :
    flg(texec S (W ⧺ U) τ) = 1 ∨ texec S (W ⧺ U) τ = σ' := by
  rw [texec_seqApp]
  rcases h with (h | h)
  · left
    exact halted_exec S U _ h
  · rw [h]
    exact hU

/-! ## Leaves -/

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma leaf_window (f : ℕ → V) (g t T : V) (i : ℕ) (hi : i < 8) :
    (last2 T 0 ((items f g t).take (i + 2))).1 = f i := by
  interval_cases i <;> rfl

lemma leaf_nohalt (f : ℕ → V) (g t T : V) (hT : T ≠ 1) (hf : ∀ j, f j ≠ 1) (i : ℕ)
    (hi : i < 8) : NoHalt T 0 ((items f g t).take (i + 2)) := by
  interval_cases i <;> simp [NoHalt, items, add_ne_one, hT, hf]

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma leaf_last (f : ℕ → V) (g t : V) (i : ℕ) (hi : i < 8)
    (hne : (items f g t).drop (i + 2) ≠ []) : ((items f g t).drop (i + 2)).getLast hne = t := by
  interval_cases i <;> rfl

lemma pops_run' (ys : List V) (hne : ys ≠ []) (t w d h δ W τ : V)
    (hW : texec S W τ = ⟪⟪t, ys.foldr cantor w, d, h⟫, δ + (ys.length : V), 0⟫) :
    texec S (pops ys.length W) τ = ⟪⟪t, w, 0, ys.getLast hne⟫, δ, 0⟫ := by
  have he : ys.dropLast ++ [ys.getLast hne] = ys := List.dropLast_append_getLast hne
  have hlen : ys.dropLast.length + 1 = ys.length := by
    have h1 := congrArg List.length he
    simpa using h1
  have h := pops_run S ys.dropLast t (ys.getLast hne) w d h δ W τ (by rw [he, hlen]; exact hW)
  rw [hlen] at h
  exact h

/-- The word for the leaf `i` with the parameters `D H A d`. -/
def LEAF (i : ℕ) (D H A d : V) : V :=
  pops (8 - i) (shifts (i + 2) (snoc (offset d DISCARD) (AX A H (D - d))))

theorem G_leaf (i : ℕ) (hi : i < 8) (D H A d : V) (hd : d ≤ D) : G S (S.leaf i D H A d) := by
  refine ⟨LEAF i D H A d, Or.inr ?_⟩
  obtain ⟨L, hL⟩ : ∃ L : List V,
      L = items (fun j => S.leaf j D H A d) (4 * cantor 0 d + 2) 0 := ⟨_, rfl⟩
  have hlen : L.length = 10 := by rw [hL]; rfl
  have h1 : texec S (offset d DISCARD) ⟪⟪0, 0, 0, 0⟫, 0, 0⟫ = ⟪⟪0, 0, d, 0⟫, 0, 0⟫ :=
    offset_run S d 0 0 DISCARD _ (discard_run S 0 0 0)
  have hD : d + (D - d) = D := add_tsub_cancel_of_le hd
  have h2 := ax_shifts S A H (D - d) 0 0 d 0 0 (L.take (i + 2)) (L.drop (i + 2))
    (by rw [hD, zero_add, ← hL]; exact (List.take_append_drop _ _).symm)
    (by
      rw [hD, zero_add, hL]
      exact leaf_nohalt _ _ _ _ (S.axT_ne_one _ _ _) (fun j => S.leaf_ne_one j _ _ _ _) i hi)
    _ _ h1
  have ht : (L.take (i + 2)).length = i + 2 := by
    rw [List.length_take, hlen]
    omega
  have hdl : (L.drop (i + 2)).length = 8 - i := by
    rw [List.length_drop, hlen]
    omega
  have hne : L.drop (i + 2) ≠ [] := by
    intro h0
    rw [h0] at hdl
    simp at hdl
    omega
  rw [ht] at h2
  have h3 := pops_run' S (L.drop (i + 2)) hne _ 0 0 _ 0 _ _ h2
  rw [hdl] at h3
  rw [LEAF, h3]
  subst hL
  rw [leaf_last _ _ _ i hi, leaf_window _ _ _ _ i hi]

/-! ## The gate -/

theorem G_axT (H D A : V) : G S (S.axT H D A) := by
  refine ⟨pops 10 (snoc DISCARD (AX A H D)), Or.inr ?_⟩
  have h1 : texec S (snoc DISCARD (AX A H D)) ⟪⟪0, 0, 0, 0⟫, 0, 0⟫ =
      ⟪⟪S.axT (0 + H) (0 + D) A,
        (items (fun i => S.leaf i (0 + D) (0 + H) A 0) (4 * cantor 0 0 + 2) 0).foldr cantor 0,
        0, 0⟫, 0 + ((10 : ℕ) : V), 0⟫ := by
    rw [texec_snoc, discard_run S 0 0 0, tstep_AX]
  have h2 := pops_run' S (items (fun i => S.leaf i (0 + D) (0 + H) A 0) (4 * cantor 0 0 + 2) 0)
    (by simp [items]) _ 0 0 0 0 _ _ h1
  simpa [items] using h2

/-! ## Generalization -/

/-- After a PUSH: label the saved formula and pop its generalization. -/
def GENTAIL (i : V) : V := shifts 10 (snoc (snoc (offset i 0) SH) (AX i 0 0))

lemma gen_run (i a v δ : V) :
    texec S (GENTAIL i) ⟪⟪0, cantor a v, 0, 0⟫, δ + 1, 0⟫ = ⟪⟪4 * cantor a i + 2, v, 0, 0⟫, δ, 0⟫ := by
  have h1 : texec S (offset i 0) ⟪⟪0, cantor a v, 0, 0⟫, δ + 1, 0⟫ =
      ⟪⟪0, cantor a v, i, 0⟫, δ + 1, 0⟫ := offset_run S i _ _ 0 _ (by simp)
  have h2 : texec S (snoc (offset i 0) SH) ⟪⟪0, cantor a v, 0, 0⟫, δ + 1, 0⟫ =
      ⟪⟪0, v, i, a⟫, δ, 0⟫ := by
    rw [texec_snoc, h1]
    exact tstep_SH S 0 0 a v i δ (by simp)
  exact ax_all S i 0 0 0 v i a δ _ _ h2

theorem G_gen (i a : V) (ha : G S a) : G S (4 * cantor a i + 2) := by
  obtain ⟨W, hW⟩ := ha
  refine ⟨W ⧺ PUSH ⧺ GENTAIL i, ?_⟩
  exact chain S (chain S hW (Or.inr (push_run S a 0 0))) (Or.inr (gen_run S i a 0 0))

/-! ## Modus ponens -/

def SH2 : V := snoc (snoc 0 SH) SH

lemma sh2_run (a c v δ : V) (ha : a ≠ 1) :
    texec S SH2 ⟪⟪0, cantor a (cantor c v), 0, 0⟫, δ + 1 + 1, 0⟫ = ⟪⟪a, v, 0, c⟫, δ, 0⟫ := by
  rw [SH2, texec_snoc, texec_snoc, texec_nil, tstep_SH S 0 0 a _ 0 (δ + 1) (by simp)]
  exact tstep_SH S 0 a c v 0 δ (by simpa using ha)

lemma sh2_halt (w δ : V) :
    flg(texec S SH2 ⟪⟪0, cantor 1 w, 0, 0⟫, δ + 1 + 1, 0⟫) = 1 := by
  rw [SH2, texec_snoc, texec_snoc, texec_nil, tstep_SH S 0 0 1 _ 0 (δ + 1) (by simp),
    tstep_SH_halt S 0 1 w 0 (δ + 1) (by simp)]
  simp

/-- After the two SHIFTs: test the implication and pop the consequent. -/
def MPSUF2 (b : V) : V := shifts 11 (snoc (snoc 0 (MP b)) (AX b 0 0))

lemma mpsuf2_run (a b v δ : V) :
    texec S (MPSUF2 b) ⟪⟪a, v, 0, 4 * cantor a b⟫, δ, 0⟫ = ⟪⟪b, v, 0, 0⟫, δ, 0⟫ := by
  have h1 : texec S (snoc 0 (MP b)) ⟪⟪a, v, 0, 4 * cantor a b⟫, δ, 0⟫ =
      ⟪⟪0 + b, cantor 0 v, 0 + b, 0⟫, δ + 1, 0⟫ := by
    rw [texec_snoc, texec_nil]
    exact tstep_MP_yes S b a v 0 _ δ (by simp)
  rw [MPSUF2, shifts_succ', texec_snoc, ax_all S b 0 0 (0 + b) (cantor 0 v) (0 + b) 0 (δ + 1) _ _ h1,
    tstep_SH S _ (0 + b) 0 v 0 δ (allV_add_ne_one _ _)]
  simp

theorem G_mp (a b : V) (ha : G S a) (hab : G S (4 * cantor a b)) : G S b := by
  obtain ⟨Wp, hp⟩ := ha
  obtain ⟨Wq, hq⟩ := hab
  refine ⟨Wq ⧺ PUSH ⧺ Wp ⧺ PUSH ⧺ SH2 ⧺ MPSUF2 b, ?_⟩
  have c1 := chain S hq (Or.inr (push_run S (4 * cantor a b) 0 0))
  have c2 := chain S c1 (good_run S hp (cantor (4 * cantor a b) 0) (0 + 1))
  have c3 := chain S c2 (Or.inr (push_run S a (cantor (4 * cantor a b) 0) (0 + 1)))
  by_cases h1 : a = 1
  · subst h1
    have c4 : flg(texec S (Wq ⧺ PUSH ⧺ Wp ⧺ PUSH ⧺ SH2) ⟪⟪0, 0, 0, 0⟫, 0, 0⟫) = 1 := by
      rw [texec_seqApp]
      rcases c3 with (h | h)
      · exact halted_exec S SH2 _ h
      · rw [h]
        exact sh2_halt S _ 0
    refine Or.inl ?_
    rw [texec_seqApp]
    exact halted_exec S _ _ c4
  · have c4 := chain S c3 (Or.inr (sh2_run S a (4 * cantor a b) 0 0 h1))
    exact chain S c4 (Or.inr (mpsuf2_run S a b 0 0))

end model

#print axioms good_run
#print axioms G_leaf
#print axioms G_axT
#print axioms G_gen
#print axioms G_mp
end ConPA.Words
