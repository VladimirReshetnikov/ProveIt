import IPRADerivations.Analysis.Exponential.Estimates.GaussianRationalExponentialTail

/-!
# The original exponential tail on the half disk

If the rational input has norm at most A/B and at most one half,
the terms starting at order N have a common factor (A/B)^N.
The remaining finite geometric majorant is bounded by two.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalExponentialSmallTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalExponentialTail (tail tail_zero tail_succ)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalPolynomialExponential (inverseFactorial)
open GaussianRationalReciprocal (power bounded_power bounded_product bounded_sum bound_congr)
open GaussianRationalSyntheticDivision (qmul_congr)
open ExponentialMajorant (Gg Gg_zero Gg_succ geom)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private def geomData : PTm n := pairT one one
private def geomNum (k : PTm n) : PTm n := Gg k geomData

private theorem geom_step (k : PTm n) : Γ ⊢[PRAAx] geomNum (succ k) ≐ two*geomNum k+one := by
  exact (Gg_succ k geomData).eqTrans (congrAdd (congrMul
    ((congrAdd (fst_pair _ _) (snd_pair _ _)).eqTrans (by ipra_ring)) (.eqRefl _))
    ((congrAp2 powF (.eqRefl _) (fst_pair _ _)).eqTrans (GaussianPolynomialPerturbation.one_power k)))

private theorem geom_bound (k : PTm n) : Γ ⊢[PRAAx] le (geomNum k) (unit k) := by
  have h := geom (Γ := Γ) k (geomData : PTm n)
  have e : Γ ⊢[PRAAx] fstT (geomData : PTm n)+sndT geomData ≐ two :=
    (congrAdd (fst_pair _ _) (snd_pair _ _)).eqTrans (by ipra_ring)
  have base : Γ ⊢[PRAAx] pw (fstT geomData+sndT geomData) k ≐ unit k :=
    congrAp2 powF (.eqRefl k) e
  have left : Γ ⊢[PRAAx] sndT geomData * geomNum k + pw (fstT geomData) k ≐ one*geomNum k+one :=
    congrAdd (congrMul (snd_pair _ _) (.eqRefl (geomNum k)))
    ((congrAp2 powF (.eqRefl k) (fst_pair _ _)).eqTrans (GaussianPolynomialPerturbation.one_power k))
  exact le_of_eq_add (d := one) (base.eqSymm.eqTrans (h.eqSymm.eqTrans (left.eqTrans (by ipra_ring))))

private theorem term_bound (q N k A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] bounded q A B) (hh : Γ ⊢[PRAAx] bounded q one two) :
    Γ ⊢[PRAAx] bounded (qmul (inverseFactorial (N+k)) (power q (N+k))) (pw A N) (pw B N*unit k) := by
  have twoPos : Γ ⊢[PRAAx] le one two := RationalAlgebra.two_positive
  have term := bounded_power q A B N hB hq
  have half := bound_congr (.eqRefl _) (GaussianPolynomialPerturbation.one_power k) (.eqRefl _)
    (bounded_power q one two k twoPos hh)
  have pwPos := GaussianFactorBudget.power_positive B N hB
  have prod := bounded_product _ _ _ _ _ _ pwPos (unit_positive k) term half
  have inv : Γ ⊢[PRAAx] bounded (inverseFactorial (N+k)) one one :=
    GaussianCoefficientNormEntries.l1_to_euclidean _ _ _ (le_refl one)
      (GaussianFiniteExponentialWeightedNorm.inverse_factorial_bound (N+k))
  have out := bounded_product _ _ _ _ _ _ (le_refl one) (positive_product _ _ pwPos (unit_positive k)) inv prod
  exact bound_congr (qmul_congr (.eqRefl _) (GaussianRationalPowerAlgebra.power_add q N k).eqSymm)
    (by ipra_ring) (by ipra_ring) out

private def budgetedTail (q N A B k : PTm n) : Fm PTm n :=
  bounded (tail q N k) (two*pw A N*geomNum k) (pw B N*unit k)

@[simp] private theorem subst_budgetedTail {m : ℕ} (σ : Fin n → PTm m) (q N A B k : PTm n) :
    (budgetedTail q N A B k).subst σ =
      budgetedTail (Syn.subst σ q) (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) := by
  simp [budgetedTail,geomNum,geomData,Gg]

private theorem start (q N A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] budgetedTail q N A B zero := by
  have hD := positive_product _ _ (GaussianFactorBudget.power_positive B N hB)
    (unit_positive zero)
  have e : Γ ⊢[PRAAx] two*pw A N*geomNum (zero : PTm n) ≐ zero :=
    (congrMul (.eqRefl _) (Gg_zero geomData)).eqTrans (mul_zero _)
  exact bound_congr (tail_zero q N).eqSymm e.eqSymm (.eqRefl _)
    (GaussianMonicResidualRadius.zero_bounded zero _ hD)

private theorem advance (q N A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] bounded q A B) (hh : Γ ⊢[PRAAx] bounded q one two)
    (ih : Γ ⊢[PRAAx] budgetedTail q N A B k) : Γ ⊢[PRAAx] budgetedTail q N A B (succ k) := by
  let D := pw B N*unit k
  let D' := pw B N*unit (succ k)
  let P := pw A N
  let G := geomNum k
  have db := GaussianFactorBudget.power_positive B N hB
  have hp : Γ ⊢[PRAAx] le one D := positive_product _ _ db (unit_positive k)
  have hn : Γ ⊢[PRAAx] le one D' := positive_product _ _ db (unit_positive (succ k))
  have eD : Γ ⊢[PRAAx] D' ≐ two*D :=
    (congrMul (.eqRefl _) (pw_succ two k)).eqTrans (by dsimp [D,unit]; ipra_ring)
  have stepN : Γ ⊢[PRAAx] two*P*geomNum (succ k) ≐ two*(two*P*G+P) :=
    (congrMul (.eqRefl _) (geom_step k)).eqTrans (by unfold G; ipra_ring)
  have hd := (congrMul (by ipra_ring : Γ ⊢[PRAAx] two*P*G*D+P*D ≐ (two*P*G+P)*D) eD).eqTrans
    (by ipra_ring : Γ ⊢[PRAAx] (two*P*G+P)*D*(two*D) ≐ (two*(two*P*G+P))*(D*D))
  have enc : Γ ⊢[PRAAx] le ((two*P*G*D+P*D)*D') (two*P*geomNum (succ k)*(D*D)) :=
    le_of_eq_add (d := zero) ((congrMul stepN (.eqRefl _)).eqTrans (hd.eqSymm.eqTrans (by ipra_ring)))
  exact bound_congr (tail_succ q N k).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (positive_product _ _ hp hp) hn enc
      (bounded_sum _ _ _ _ _ _ hp hp ih (term_bound q N k A B hB hq hh)))

theorem small_tail (q N A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] bounded q A B) (hh : Γ ⊢[PRAAx] bounded q one two) :
    Γ ⊢[PRAAx] bounded (tail q N k) (two*pw A N) (pw B N) := by
  let sh (t : PTm n) := Syn.shift t
  have ds : Γ.map Fm.shift ⊢[PRAAx] le one (sh B) :=
    by simpa [Fm.shift,Syn.shift,sh,one] using hB.shift
  have qs : Γ.map Fm.shift ⊢[PRAAx] bounded (sh q) (sh A) (sh B) :=
    by simpa [Fm.shift,Syn.shift,sh] using hq.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] bounded (sh q) one two :=
    by simpa [Fm.shift,Syn.shift,sh,one,two] using hh.shift
  have all : Γ ⊢[PRAAx] .all (budgetedTail (sh q) (sh N) (sh A) (sh B) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [sh,subst_budgetedTail,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using start q N A B hB
    · simp only [sh,subst_budgetedTail,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact advance _ _ _ _ _ ds.wk qs.wk hs.wk Prf.hyp0
  have tailBound : Γ ⊢[PRAAx] budgetedTail q N A B k := by
    simpa only [sh,subst_budgetedTail,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  have pos := GaussianFactorBudget.power_positive B N hB
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ pos (unit_positive k)) pos (by
      let val := fun t : PTm n => Groth.ι (Q.mk Γ t)
      ipra_le 2*val (pw A N)*val (pw B N)*sl (geom_bound k)) tailBound

theorem actual_small_exponential_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ bounded (var 0) (var 2) (var 3) ⟶ bounded (var 0) one two ⟶
      bounded (tail (var 0) (var 1) (var 4)) (two*pw (var 2) (var 1)) (pw (var 3) (var 1))) :=
  closeUniv 5 (.impI (.impI (.impI (small_tail _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianRationalExponentialSmallTail
