import Diophantine.Paper1982.Pair40
import Diophantine.Paper1982.UniversalQuartic

/-!
# Universal pairs

`UniversalPair ν δ`: one integer polynomial in three index parameters, the input and `ν`
witnesses, whose specialization at the parameters has total degree at most `δ` (counting the
input and the witnesses), represents every recursively enumerable set on positive inputs.
This is the convention of 1982 §5; the 1978 definition, where the input also does not count
towards the degree, is weaker.

* `universalPair_mono`: `(ν, δ)` universal implies `(ν', δ')` universal for `ν ≤ ν'`, `δ ≤ δ'`;
* `universalPair_58_4` (1982 §5) and `universalPair_40_8` (eighteen witnesses eliminated);
* `jones1978_pairs`: every pair of the 1978 table.
-/

namespace Jones1982

open MvPolynomial

/-- Substitute the three index parameters. -/
noncomputable def specializeN {ν : ℕ} (p : Fin 3 → ℤ) (U : MvPolynomial (Fin 3 ⊕ Fin (ν + 1)) ℤ) :
    MvPolynomial (Fin (ν + 1)) ℤ :=
  eval₂ C (Sum.elim (fun i => C (p i)) X) U

theorem eval_specializeN {ν : ℕ} (p : Fin 3 → ℤ) (a : Fin (ν + 1) → ℤ)
    (U : MvPolynomial (Fin 3 ⊕ Fin (ν + 1)) ℤ) :
    eval a (specializeN p U) = eval (Sum.elim p a) U := by
  unfold specializeN
  rw [← eval_assoc]
  apply congrArg (fun f => eval f U)
  funext i
  cases i <;> simp

/-- A universal pair. -/
def UniversalPair (ν δ : ℕ) : Prop :=
  ∃ U : MvPolynomial (Fin 3 ⊕ Fin (ν + 1)) ℤ,
    (∀ p : Fin 3 → ℕ, (specializeN (fun i => (p i : ℤ)) U).totalDegree ≤ δ) ∧
    ∀ S : Set ℕ, REPred S → ∃ p : Fin 3 → ℕ, ∀ x : ℕ, 0 < x →
      (x ∈ S ↔ ∃ a : Fin ν → ℕ,
        eval (fun k => ((Fin.cons x a : Fin (ν + 1) → ℕ) k : ℤ))
          (specializeN (fun i => (p i : ℤ)) U) = 0)

theorem wset_iff_cons {ν : ℕ} (Q : MvPolynomial (Fin (ν + 1)) ℤ) (x : ℕ) :
    Wset Q x ↔ ∃ a : Fin ν → ℕ, eval (fun k => ((Fin.cons x a : Fin (ν + 1) → ℕ) k : ℤ)) Q = 0 := by
  constructor
  · rintro ⟨zs, h0, hz⟩
    refine ⟨fun i => zs i.succ, ?_⟩
    convert hz using 3
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp [h0]
    · simp
  · rintro ⟨a, ha⟩
    exact ⟨Fin.cons x a, rfl, ha⟩

theorem specializeN_rename {ν ν' : ℕ} (h : ν + 1 ≤ ν' + 1) (p : Fin 3 → ℤ)
    (U : MvPolynomial (Fin 3 ⊕ Fin (ν + 1)) ℤ) :
    specializeN p (rename (Sum.map id (Fin.castLE h)) U) = rename (Fin.castLE h) (specializeN p U) := by
  induction U using MvPolynomial.induction_on with
  | C a => simp only [specializeN, rename_C, eval₂_C]
  | add p q hp hq => simp only [map_add, specializeN, eval₂_add] at hp hq ⊢; rw [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, specializeN, eval₂_mul] at hp ⊢
    rw [hp]
    cases i <;> simp

/-- Monotonicity of universal pairs. -/
theorem universalPair_mono {ν δ ν' δ' : ℕ} (h : UniversalPair ν δ) (hν : ν ≤ ν') (hδ : δ ≤ δ') :
    UniversalPair ν' δ' := by
  obtain ⟨U, hdeg, hrep⟩ := h
  have h1 : ν + 1 ≤ ν' + 1 := by omega
  refine ⟨rename (Sum.map id (Fin.castLE h1)) U, fun p => ?_, fun S hS => ?_⟩
  · rw [specializeN_rename]
    exact (totalDegree_rename_le _ _).trans ((hdeg p).trans hδ)
  · obtain ⟨p, hp⟩ := hrep S hS
    refine ⟨p, fun x hx => (hp x hx).trans ?_⟩
    simp only [specializeN_rename, eval_rename]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨fun i => if hi : i.val < ν then a ⟨i.val, hi⟩ else 0, ?_⟩
      convert ha using 3
      funext k
      refine Fin.cases ?_ (fun i => ?_) k
      · rfl
      · rw [Function.comp_apply, show Fin.castLE h1 i.succ = (Fin.castLE hν i).succ from rfl,
          Fin.cons_succ, Fin.cons_succ]
        simp [Fin.castLE, i.isLt]
    · rintro ⟨a, ha⟩
      refine ⟨fun i => a (Fin.castLE hν i), ?_⟩
      convert ha using 3
      funext k
      refine Fin.cases ?_ (fun i => ?_) k
      · rfl
      · rw [Function.comp_apply, show Fin.castLE h1 i.succ = (Fin.castLE hν i).succ from rfl,
          Fin.cons_succ, Fin.cons_succ]

/-- **(58, 4)** (1982 §5). -/
theorem universalPair_58_4 : UniversalPair 58 4 := by
  obtain ⟨U, hdeg, hrep⟩ := universal_quartic58
  have hp : ∀ p : Fin 3 → ℕ, (fun i => (p i : ℤ)) = ![(p 0 : ℤ), (p 1 : ℤ), (p 2 : ℤ)] := by
    intro p; funext i; fin_cases i <;> rfl
  refine ⟨U, fun p => ?_, fun S hS => ?_⟩
  · rw [hp]; exact hdeg (p 0) (p 1) (p 2)
  · obtain ⟨z, u, y, -, -, -, -, h⟩ := hrep S hS
    refine ⟨![z, u, y], fun x hx => (h x hx).trans ?_⟩
    rw [hp]
    exact wset_iff_cons _ x

namespace Pair40

open ShortQuadratic ShortQuadraticExpr

private theorem isPoly_pow {α : Type*} {f : (α → ℕ) → ℤ}
    (hf : IsPoly f) (n : ℕ) : IsPoly (fun v => f v ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using (IsPoly.const (α := α) 1)
  | succ n ih => simpa only [pow_succ] using ih.mul hf

private theorem isPoly_sum {α β : Type*} (s : Finset β)
    (f : β → (α → ℕ) → ℤ) :
    (∀ i ∈ s, IsPoly (f i)) → IsPoly (fun v => ∑ i ∈ s, f i v) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa only [Finset.sum_empty] using (IsPoly.const (α := α) 0)
  | @insert i s hi ih =>
      intro hf
      have hfi := hf i (Finset.mem_insert_self i s)
      have hfs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi, zero_sub, sub_neg_eq_add] using
        hfi.sub ((IsPoly.const 0).sub hfs)

private def witnessEval (v : Fin 3 ⊕ Fin 41 → ℕ) : Option ShortQuadraticVar → ℤ :=
  fun o => (v (Sum.inr (coord o)) : ℤ)

set_option maxHeartbeats 8000000 in
private theorem redShift_isPoly (L : ℕ) (i : ShortQuadraticEquation) (hi : kept i = true) :
    IsPoly (fun v : Fin 3 ⊕ Fin 41 → ℕ =>
      MvPolynomial.eval (witnessEval v)
        (redShift (v (Sum.inl 0)) (v (Sum.inl 1)) (v (Sum.inl 2)) L i)) := by
  cases i <;> first | exact absurd hi (by decide) |
    (simp only [redShift, ShortQuadraticExpr.eval_shiftWitnesses, redExpr, expression,
      ShortQuadraticExpr.subst_add, ShortQuadraticExpr.subst_sub, ShortQuadraticExpr.subst_mul,
      ShortQuadraticExpr.subst_pow, ShortQuadraticExpr.subst_ofNat, subst, full, σ₁, defn, elim,
      bExpr, AExpr, CExpr, QExpr, ShortQuadraticExpr.toPolynomial_add,
      ShortQuadraticExpr.toPolynomial_sub, ShortQuadraticExpr.toPolynomial_mul,
      ShortQuadraticExpr.toPolynomial_pow, ShortQuadraticExpr.toPolynomial_ofNat,
      Bool.false_eq_true, ↓reduceIte, ShortQuadraticExpr.toPolynomial,
      MvPolynomial.eval_C, MvPolynomial.eval_X, map_add, map_sub, map_mul, map_pow,
      shiftAssignment, witnessEval]
     repeat' first
      | exact IsPoly.proj _
      | exact IsPoly.const _
      | apply IsPoly.neg
      | apply IsPoly.add
      | apply IsPoly.sub
      | apply IsPoly.mul
      | apply isPoly_pow)

private theorem octic_isPoly (L : ℕ) :
    IsPoly (fun v : Fin 3 ⊕ Fin 41 → ℕ =>
      MvPolynomial.eval (fun i : Fin 41 => (v (Sum.inr i) : ℤ))
        (octic40 (v (Sum.inl 0)) (v (Sum.inl 1)) (v (Sum.inl 2)) L)) := by
  simp only [octic40, MvPolynomial.eval_rename, redSum, map_sum, map_pow]
  exact isPoly_sum _ _ (fun i hi => isPoly_pow (redShift_isPoly L i (Finset.mem_filter.1 hi).2) 2)

noncomputable def jointOctic : MvPolynomial (Fin 3 ⊕ Fin 41) ℤ :=
  Classical.choose (Diophantine.isPoly_iff_exists_mvPolynomial.mp (octic_isPoly (L4 58)))

theorem eval_jointOctic (v : Fin 3 ⊕ Fin 41 → ℕ) :
    MvPolynomial.eval (fun i => (v i : ℤ)) jointOctic =
      MvPolynomial.eval (fun i : Fin 41 => (v (Sum.inr i) : ℤ))
        (octic40 (v (Sum.inl 0)) (v (Sum.inl 1)) (v (Sum.inl 2)) (L4 58)) :=
  Classical.choose_spec (Diophantine.isPoly_iff_exists_mvPolynomial.mp (octic_isPoly (L4 58))) v

private theorem eq_of_eval_nat_eq {α : Type*} {p q : MvPolynomial α ℤ}
    (h : ∀ a : α → ℕ, eval (fun i => (a i : ℤ)) p = eval (fun i => (a i : ℤ)) q) : p = q := by
  classical
  apply MvPolynomial.funext_set (fun _ : α => Set.range (fun n : ℕ => (n : ℤ)))
    (fun _ => Set.infinite_range_of_injective (Nat.cast_injective (R := ℤ)))
  intro a ha
  have hex : ∀ i : α, ∃ n : ℕ, (n : ℤ) = a i := fun i => ha i (Set.mem_univ i)
  choose b hb using hex
  have hab : a = fun i => (b i : ℤ) := funext (fun i => (hb i).symm)
  rw [hab]
  exact h b

theorem specializeN_jointOctic (p : Fin 3 → ℕ) :
    specializeN (fun i => (p i : ℤ)) jointOctic = octic40 (p 0) (p 1) (p 2) (L4 58) := by
  apply eq_of_eval_nat_eq
  intro a
  rw [eval_specializeN]
  have h := eval_jointOctic (Sum.elim p a)
  have hv : (fun i : Fin 3 ⊕ Fin 41 => ((Sum.elim p a i : ℕ) : ℤ)) =
      Sum.elim (fun i => (p i : ℤ)) (fun i => (a i : ℤ)) := by
    funext i; cases i <;> rfl
  rw [hv] at h
  simpa using h

end Pair40

/-- **(40, 8)**. -/
theorem universalPair_40_8 : UniversalPair 40 8 := by
  refine ⟨Pair40.jointOctic, fun p => ?_, fun S hS => ?_⟩
  · rw [Pair40.specializeN_jointOctic]; exact Pair40.octic40_totalDegree_le _ _ _ _
  · obtain ⟨z, u, y, hz, -, -, -, -, h⟩ := rePred_quartic58_family hS
    refine ⟨![z, u, y], fun x hx => (h x hx).trans ?_⟩
    rw [Pair40.specializeN_jointOctic, ShortQuadratic.wset_quartic58_iff]
    exact (Pair40.exists_octic40_iff hz).symm

/-- **The universal pairs of the 1978 table** (in the stronger 1982 convention). -/
theorem jones1978_pairs :
    ∀ pr ∈ [(108, 4), (80, 8), (70, 12), (65, 16), (62, 20), (56, 24), (49, 56), (48, 60),
      (47, 80), (46, 84), (45, 108), (44, 144), (43, 156), (42, 300), (41, 348), (40, 1380)],
      UniversalPair pr.1 pr.2 := by
  intro pr hpr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
  rcases hpr with rfl | hpr
  · exact universalPair_mono universalPair_58_4 (by norm_num) (by norm_num)
  · have h8 : 8 ≤ pr.2 ∧ 40 ≤ pr.1 := by
      rcases hpr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> norm_num
    exact universalPair_mono universalPair_40_8 h8.2 h8.1

end Jones1982
