import ConPACtlGadgets
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
namespace ConPA.Ctl
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

/-! ## Selecting an entry of an AX -/

/-- AX on the store `⟪0, 0, d, 0⟫`, then `m` SHIFTs, then POPs of the remaining entries: the
top is what the SHIFTs leave there. -/
lemma select_run (A H x d : V) (m : ℕ) (ys : List V) (r W : V) (hm : m ≤ S.n)
    (hdrop : (itemsL S (S.axT (0 + H) (d + x) A) (fun j => S.leaf j (d + x) (0 + H) A d)
      (4 * cantor 0 (S.genL A d) + 2) 0).drop m = ys ++ [0])
    (hno : NoHalt S (topL S (S.axT (0 + H) (d + x) A)) 0
      ((itemsL S (S.axT (0 + H) (d + x) A) (fun j => S.leaf j (d + x) (0 + H) A d)
        (4 * cantor 0 (S.genL A d) + 2) 0).take m))
    (hr : (last2 (topL S (S.axT (0 + H) (d + x) A)) 0
      ((itemsL S (S.axT (0 + H) (d + x) A) (fun j => S.leaf j (d + x) (0 + H) A d)
        (4 * cantor 0 (S.genL A d) + 2) 0).take m)).1 = r) (hr1 : r ≠ 1)
    (hW : texec S W ⟪⟪0, 0, 0, 0⟫, 0, 0⟫ = ⟪⟪0, 0, d, 0⟫, 0, 0⟫) :
    texec S (pops S (ys.length + 1) (shifts m (snoc W (AX A H x)))) ⟪⟪0, 0, 0, 0⟫, 0, 0⟫ =
      ⟪⟪r, 0, 0, 0⟫, 0, 0⟫ := by
  have h2 := ax_shifts S A H x 0 0 d 0 0 _ _ (List.take_append_drop m _).symm hno W _ hW
  have ht : ((itemsL S (S.axT (0 + H) (d + x) A) (fun j => S.leaf j (d + x) (0 + H) A d)
      (4 * cantor 0 (S.genL A d) + 2) 0).take m).length = m := by
    rw [List.length_take, itemsL_length]
    exact Nat.min_eq_left hm
  rw [ht, hdrop, hr, List.length_append, List.length_singleton] at h2
  exact pops_run S ys r 0 0 0 _ 0 _ _ hr1 h2

/-! ## Leaves -/

lemma leaf_le (i : ℕ) (hi : i < S.m) : i + 2 + S.g ≤ S.n := by
  revert hi
  unfold Sem.g Sem.n Sem.m
  cases S.ax11 <;> cases S.short <;> simp <;> omega

lemma leaf_window (f : ℕ → V) (g t T : V) (i : ℕ) (hi : i < S.m) :
    (last2 (topL S T) 0 ((itemsL S T f g t).take (i + 2 + S.g))).1 = f i := by
  revert hi
  unfold topL itemsL items Sem.g Sem.m
  cases S.ax11 <;> cases S.short <;> intro hi <;>
    simp only [Bool.false_eq_true, ↓reduceIte] at hi <;> interval_cases i <;> rfl

lemma leaf_nohalt (f : ℕ → V) (g t T : V) (hT : T ≠ 1) (hf : ∀ j, f j ≠ 1) (i : ℕ)
    (hi : i < S.m) : NoHalt S (topL S T) 0 ((itemsL S T f g t).take (i + 2 + S.g)) := by
  revert hi
  unfold topL itemsL items Sem.g Sem.m
  cases S.ax11 <;> cases S.short <;> intro hi <;>
    simp only [Bool.false_eq_true, ↓reduceIte] at hi <;> interval_cases i <;>
    simp [NoHalt, halts_iff_false, hT, hf]

lemma leaf_drop (f : ℕ → V) (g t T : V) (i : ℕ) (hi : i < S.m) :
    ∃ ys : List V, (itemsL S T f g t).drop (i + 2 + S.g) = ys ++ [t] ∧
      ys.length + 1 = S.m - i := by
  refine ⟨((itemsL S T f g t).drop (i + 2 + S.g)).dropLast, ?_, ?_⟩ <;>
    (revert hi; unfold itemsL items Sem.g Sem.m
     cases S.ax11 <;> cases S.short <;> intro hi <;>
       simp only [Bool.false_eq_true, ↓reduceIte] at hi <;> interval_cases i <;> rfl)

/-- The word for the leaf `i` with the parameters `D H A d`. -/
def LEAF (i : ℕ) (D H A d : V) : V :=
  pops S (S.m - i) (shifts (i + 2 + S.g) (snoc (offset d (DISCARD S)) (AX A H (D - d))))

theorem G_leaf (i : ℕ) (hi : i < S.m) (D H A d : V) (hd : d ≤ D) :
    G S (S.leaf i D H A d) := by
  refine ⟨LEAF S i D H A d, Or.inr ?_⟩
  have h1 : texec S (offset d (DISCARD S)) ⟪⟪0, 0, 0, 0⟫, 0, 0⟫ = ⟪⟪0, 0, d, 0⟫, 0, 0⟫ :=
    offset_run S d 0 0 (DISCARD S) _ (discard_run S 0 0 0)
  have hD : d + (D - d) = D := add_tsub_cancel_of_le hd
  obtain ⟨ys, hys, hylen⟩ := leaf_drop S (fun j => S.leaf j (d + (D - d)) (0 + H) A d)
    (4 * cantor 0 (S.genL A d) + 2) 0 (S.axT (0 + H) (d + (D - d)) A) i hi
  have h := select_run S A H (D - d) d (i + 2 + S.g) ys
    (S.leaf i (d + (D - d)) (0 + H) A d) _ (leaf_le S i hi) hys
    (leaf_nohalt S _ _ _ _ (S.axT_ne_one _ _ _) (fun j => S.leaf_ne_one j _ _ _ _) i hi)
    (leaf_window S _ _ _ _ i hi) (S.leaf_ne_one i _ _ _ _) h1
  rw [hylen, hD, zero_add] at h
  exact h

/-! ## The gate -/

lemma gate_le : 2 * S.g ≤ S.n := by
  unfold Sem.g Sem.n
  cases S.ax11 <;> cases S.short <;> simp

lemma gate_window (f : ℕ → V) (g t T : V) :
    (last2 (topL S T) 0 ((itemsL S T f g t).take (2 * S.g))).1 = T := by
  unfold topL itemsL items Sem.g
  cases S.ax11 <;> cases S.short <;> rfl

lemma gate_nohalt (f : ℕ → V) (g t T : V) (hT : T ≠ 1) :
    NoHalt S (topL S T) 0 ((itemsL S T f g t).take (2 * S.g)) := by
  unfold topL itemsL items Sem.g
  cases S.ax11 <;> cases S.short <;> simp [NoHalt, halts_iff_false, hT]

lemma gate_drop (f : ℕ → V) (g t T : V) :
    ∃ ys : List V, (itemsL S T f g t).drop (2 * S.g) = ys ++ [t] := by
  refine ⟨((itemsL S T f g t).drop (2 * S.g)).dropLast, ?_⟩
  unfold itemsL items Sem.g
  cases S.ax11 <;> cases S.short <;> rfl

/-- The gate: it is the top after AX, or the first stack entry in the eleven-entry layout,
where two SHIFTs bring it to the top. -/
theorem G_axT (H D A : V) : G S (S.axT H D A) := by
  obtain ⟨ys, hys⟩ := gate_drop S (fun j => S.leaf j (0 + D) (0 + H) A 0)
    (4 * cantor 0 (S.genL A 0) + 2) 0 (S.axT (0 + H) (0 + D) A)
  refine ⟨pops S (ys.length + 1) (shifts (2 * S.g) (snoc (DISCARD S) (AX A H D))), Or.inr ?_⟩
  have h := select_run S A H D 0 (2 * S.g) ys (S.axT (0 + H) (0 + D) A) _ (gate_le S) hys
    (gate_nohalt S _ _ _ _ (S.axT_ne_one _ _ _)) (gate_window S _ _ _ _)
    (S.axT_ne_one _ _ _) (discard_run S 0 0 0)
  simpa using h

/-! ## Generalization -/

/-- After a PUSH: label the saved formula and pop its generalization. -/
def GENTAIL (i : V) : V := shifts S.n (snoc (snoc (offset i 0) SH) (AX i 0 0))

lemma gen_run (i a v δ : V) :
    texec S (GENTAIL S i) ⟪⟪0, cantor a v, 0, 0⟫, δ + 1, 0⟫ =
      ⟪⟪4 * cantor a i + 2, v, 0, 0⟫, δ, 0⟫ := by
  have h1 : texec S (offset i 0) ⟪⟪0, cantor a v, 0, 0⟫, δ + 1, 0⟫ =
      ⟪⟪0, cantor a v, i, 0⟫, δ + 1, 0⟫ := offset_run S i _ _ 0 _ (by simp)
  have h2 : texec S (snoc (offset i 0) SH) ⟪⟪0, cantor a v, 0, 0⟫, δ + 1, 0⟫ =
      ⟪⟪0, v, i, a⟫, δ, 0⟫ := by
    rw [texec_snoc, h1]
    exact tstep_SH S 0 0 a v i δ (by simp [halts_zero_iff])
  have h := ax_all S i 0 0 0 v i a δ _ _ h2
  rwa [S.genL_self] at h

theorem G_gen (i a : V) (ha : G S a) : G S (4 * cantor a i + 2) := by
  obtain ⟨W, hW⟩ := ha
  refine ⟨W ⧺ PUSH S ⧺ GENTAIL S i, ?_⟩
  exact chain S (chain S hW (Or.inr (push_run S a 0 0))) (Or.inr (gen_run S i a 0 0))

/-! ## Modus ponens -/

def SH2 : V := snoc (snoc 0 SH) SH

lemma sh2_run (a c v δ : V) (ha : a ≠ 1) :
    texec S SH2 ⟪⟪0, cantor a (cantor c v), 0, 0⟫, δ + 1 + 1, 0⟫ = ⟪⟪a, v, 0, c⟫, δ, 0⟫ := by
  rw [SH2, texec_snoc, texec_snoc, texec_nil,
    tstep_SH S 0 0 a _ 0 (δ + 1) (by simp [halts_zero_iff])]
  exact tstep_SH S 0 a c v 0 δ (by simpa [halts_zero_iff] using ha)

lemma sh2_halt (w δ : V) :
    flg(texec S SH2 ⟪⟪0, cantor 1 w, 0, 0⟫, δ + 1 + 1, 0⟫) = 1 := by
  rw [SH2, texec_snoc, texec_snoc, texec_nil,
    tstep_SH S 0 0 1 _ 0 (δ + 1) (by simp [halts_zero_iff]),
    tstep_SH_halt S 0 1 w 0 (δ + 1) (by simp [halts_zero_iff])]
  simp

/-- After the two SHIFTs: test the implication and pop the consequent. For the MP kinds
`push` and `top`. -/
def MPSUF2 (b : V) : V := shifts (S.n + 1) (snoc (snoc 0 (MP b)) (AX b 0 0))

/-- After the two SHIFTs, for the MP kind `cache`: the consequent is in the cache, and one
SHIFT moves it to the top. -/
def MPSUFC (b : V) : V := snoc (snoc 0 (MP b)) SH

/-- The part of `MPSUF2` after its MP: the consequent is in `t` and `d` and a zero is on the
stack. The AX and its SHIFTs clear `d`; the last SHIFT has the consequent in the cache, so it
halts or removes the zero. -/
lemma mpsuf2_tail (b v δ W τ : V)
    (hW : texec S W τ = ⟪⟪0 + b, cantor 0 v, 0 + b, 0⟫, δ + 1, 0⟫) :
    flg(texec S (shifts (S.n + 1) (snoc W (AX b 0 0))) τ) = 1 ∨
      texec S (shifts (S.n + 1) (snoc W (AX b 0 0))) τ = ⟪⟪b, v, 0, 0⟫, δ, 0⟫ := by
  rw [shifts_succ', texec_snoc, ax_all S b 0 0 (0 + b) (cantor 0 v) (0 + b) 0 (δ + 1) _ _ hW]
  by_cases hH : S.Halts (4 * cantor 0 (S.genL b (0 + b)) + 2) (0 + b)
  · left
    rw [tstep_SH_halt S _ _ _ _ _ hH]
    simp
  · right
    rw [tstep_SH S _ (0 + b) 0 v 0 δ hH]
    simp

/-- With the push, the successful MP supplies the zero that the last SHIFT removes. -/
lemma mpsuf2_run (hk : S.mp = MPKind.push) (a b v δ : V) :
    flg(texec S (MPSUF2 S b) ⟪⟪a, v, 0, 4 * cantor a b⟫, δ, 0⟫) = 1 ∨
      texec S (MPSUF2 S b) ⟪⟪a, v, 0, 4 * cantor a b⟫, δ, 0⟫ = ⟪⟪b, v, 0, 0⟫, δ, 0⟫ := by
  unfold MPSUF2
  apply mpsuf2_tail S b v δ (snoc 0 (MP b))
  rw [texec_snoc, texec_nil, tstep_MP_yes S b a v 0 _ δ (by simp)]
  simp [mpStore, Sem.up, hk]

/-- Without the push, a zero reserved below the premises takes its place. -/
lemma mpsuf2_run' (hk : S.mp = MPKind.top) (a b v δ : V) :
    flg(texec S (MPSUF2 S b) ⟪⟪a, cantor 0 v, 0, 4 * cantor a b⟫, δ + 1, 0⟫) = 1 ∨
      texec S (MPSUF2 S b) ⟪⟪a, cantor 0 v, 0, 4 * cantor a b⟫, δ + 1, 0⟫ =
        ⟪⟪b, v, 0, 0⟫, δ, 0⟫ := by
  unfold MPSUF2
  apply mpsuf2_tail S b v δ (snoc 0 (MP b))
  rw [texec_snoc, texec_nil, tstep_MP_yes S b a (cantor 0 v) 0 _ (δ + 1) (by simp)]
  simp [mpStore, Sem.up, hk]

/-- With the result in the cache, the SHIFT after the MP halts or removes the reserved
zero. -/
lemma mpsufc_run (hk : S.mp = MPKind.cache) (a b v δ : V) :
    flg(texec S (MPSUFC b) ⟪⟪a, cantor 0 v, 0, 4 * cantor a b⟫, δ + 1, 0⟫) = 1 ∨
      texec S (MPSUFC b) ⟪⟪a, cantor 0 v, 0, 4 * cantor a b⟫, δ + 1, 0⟫ =
        ⟪⟪b, v, 0, 0⟫, δ, 0⟫ := by
  have e : tstep S (MP b) ⟪⟪a, cantor 0 v, 0, 4 * cantor a b⟫, δ + 1, 0⟫ =
      ⟪⟪0, cantor 0 v, 0, 0 + b⟫, δ + 1, 0⟫ := by
    rw [tstep_MP_yes S b a (cantor 0 v) 0 _ (δ + 1) (by simp)]
    simp [mpStore, Sem.up, hk]
  rw [MPSUFC, texec_snoc, texec_snoc, texec_nil, e]
  by_cases hH : S.Halts 0 (0 + b)
  · left
    rw [tstep_SH_halt S _ _ _ _ _ hH]
    simp
  · right
    rw [tstep_SH S 0 (0 + b) 0 v 0 δ hH]
    simp

/-- The two premises on the empty stack, and the two SHIFTs that bring them into the top and
the cache. -/
lemma mp_prefix {Wp Wq a b : V} (hp : Good S Wp a) (hq : Good S Wq (4 * cantor a b)) :
    flg(texec S (Wq ⧺ PUSH S ⧺ Wp ⧺ PUSH S ⧺ SH2) ⟪⟪0, 0, 0, 0⟫, 0, 0⟫) = 1 ∨
      texec S (Wq ⧺ PUSH S ⧺ Wp ⧺ PUSH S ⧺ SH2) ⟪⟪0, 0, 0, 0⟫, 0, 0⟫ =
        ⟪⟪a, 0, 0, 4 * cantor a b⟫, 0, 0⟫ := by
  have c1 := chain S hq (Or.inr (push_run S (4 * cantor a b) 0 0))
  have c2 := chain S c1 (good_run S hp (cantor (4 * cantor a b) 0) (0 + 1))
  have c3 := chain S c2 (Or.inr (push_run S a (cantor (4 * cantor a b) 0) (0 + 1)))
  by_cases h1 : a = 1
  · subst h1
    left
    rw [texec_seqApp]
    rcases c3 with (h | h)
    · exact halted_exec S SH2 _ h
    · rw [h]
      exact sh2_halt S _ 0
  · exact chain S c3 (Or.inr (sh2_run S a (4 * cantor a b) 0 0 h1))

/-- The same on a stack that holds a reserved zero. -/
lemma mp_prefix_reserved {Wp Wq a b : V} (hp : Good S Wp a)
    (hq : Good S Wq (4 * cantor a b)) :
    flg(texec S (PUSH S ⧺ Wq ⧺ PUSH S ⧺ Wp ⧺ PUSH S ⧺ SH2) ⟪⟪0, 0, 0, 0⟫, 0, 0⟫) = 1 ∨
      texec S (PUSH S ⧺ Wq ⧺ PUSH S ⧺ Wp ⧺ PUSH S ⧺ SH2) ⟪⟪0, 0, 0, 0⟫, 0, 0⟫ =
        ⟪⟪a, cantor 0 0, 0, 4 * cantor a b⟫, 0 + 1, 0⟫ := by
  have c0 : flg(texec S (PUSH S) ⟪⟪0, 0, 0, 0⟫, 0, 0⟫) = 1 ∨
      texec S (PUSH S) ⟪⟪0, 0, 0, 0⟫, 0, 0⟫ = ⟪⟪0, cantor 0 0, 0, 0⟫, 0 + 1, 0⟫ :=
    Or.inr (push_run S 0 0 0)
  have c1 := chain S c0 (good_run S hq (cantor 0 0) (0 + 1))
  have c2 := chain S c1 (Or.inr (push_run S (4 * cantor a b) (cantor 0 0) (0 + 1)))
  have c3 := chain S c2 (good_run S hp (cantor (4 * cantor a b) (cantor 0 0)) (0 + 1 + 1))
  have c4 := chain S c3
    (Or.inr (push_run S a (cantor (4 * cantor a b) (cantor 0 0)) (0 + 1 + 1)))
  by_cases h1 : a = 1
  · subst h1
    left
    rw [texec_seqApp]
    rcases c4 with (h | h)
    · exact halted_exec S SH2 _ h
    · rw [h]
      exact sh2_halt S _ (0 + 1)
  · exact chain S c4 (Or.inr (sh2_run S a (4 * cantor a b) (cantor 0 0) (0 + 1) h1))

theorem G_mp (a b : V) (ha : G S a) (hab : G S (4 * cantor a b)) : G S b := by
  obtain ⟨Wp, hp⟩ := ha
  obtain ⟨Wq, hq⟩ := hab
  cases hk : S.mp
  · exact ⟨Wq ⧺ PUSH S ⧺ Wp ⧺ PUSH S ⧺ SH2 ⧺ MPSUF2 S b,
      chain S (mp_prefix S hp hq) (mpsuf2_run S hk a b 0 0)⟩
  · exact ⟨PUSH S ⧺ Wq ⧺ PUSH S ⧺ Wp ⧺ PUSH S ⧺ SH2 ⧺ MPSUF2 S b,
      chain S (mp_prefix_reserved S hp hq) (mpsuf2_run' S hk a b 0 0)⟩
  · exact ⟨PUSH S ⧺ Wq ⧺ PUSH S ⧺ Wp ⧺ PUSH S ⧺ SH2 ⧺ MPSUFC b,
      chain S (mp_prefix_reserved S hp hq) (mpsufc_run S hk a b 0 0)⟩

end model

#print axioms good_run
#print axioms G_leaf
#print axioms G_axT
#print axioms G_gen
#print axioms G_mp
end ConPA.Ctl
