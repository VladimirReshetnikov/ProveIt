import IPRADerivations.Analysis.Trigonometry.SineProducts.Roots.GaussianSineSampleRootList
import IPRADerivations.Analysis.Trigonometry.SineProducts.Roots.GaussianSineRootNormalization

/-!
# The normalized product of the actual sampled sine factors

The normalized factors are folded at the same indices as the
backward polynomial product. Every sampled sine margin supplies exact
multiplication by the corresponding value of the factor at four.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSineNormalizedSampleProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianArctangentDivisionAngleResidual (sineSample rootSample)
open GaussianNameReciprocal (lower inverse_bound)
open GaussianRationalFiniteProduct (qprod product_zero product_succ product_canonical)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalLowerBounds (product_lower name_lower)
open GaussianRationalMetric (bounded qsub)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalPowerAlgebra (qmul_commutative qmul_shuffle)
open GaussianRationalReciprocal (qone qone_bounded reciprocal bounded_difference bounded_product bound_congr)
open GaussianRationalReconstruction (product factors factors_zero factors_succ)
open GaussianRationalSyntheticDivision (qone_canonical qsub_congr qmul_congr)
open GaussianReciprocalHorner (qmul_one_right)
open GaussianSineRootNormalization (normalizedFactor root_factor_normalization)
open GaussianSineSampleRootList (roots roots_at sineMargins sine_margin_at)
open GaussianSineSquaredTrace (fromSine)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (p J z s : PTm n) : PTm n := pairT p (pairT J (pairT z s))
def body : PTm 2 := normalizedFactor (sndT (sndT (sndT (var 1))))
  (sineSample (fstT (var 1)) (succ (monus (fstT (sndT (var 1))) (succ (var 0))))
    (fstT (sndT (var 1))) (fstT (sndT (sndT (var 1)))))
def normalizedPrefix (p J z s k : PTm n) : PTm n := qprod body k (data p J z s)
def normalizedProduct (p J z s : PTm n) : PTm n := normalizedPrefix p J z s J
def factorBudget (B D : PTm n) : PTm n := one+(B*B)*(D*D)
def productBudget (B D J : PTm n) : PTm n := pw (factorBudget B D) J

@[simp] theorem subst_normalizedPrefix {l : ℕ} (σ : Fin n → PTm l) (p J z s k : PTm n) :
    Syn.subst σ (normalizedPrefix p J z s k) =
      normalizedPrefix (Syn.subst σ p) (Syn.subst σ J) (Syn.subst σ z) (Syn.subst σ s) (Syn.subst σ k) := by
  simp [normalizedPrefix,data]

@[simp] theorem subst_normalizedProduct {l : ℕ} (σ : Fin n → PTm l) (p J z s : PTm n) :
    Syn.subst σ (normalizedProduct p J z s) = normalizedProduct (Syn.subst σ p) (Syn.subst σ J) (Syn.subst σ z) (Syn.subst σ s) :=
  by simp [normalizedProduct]

@[simp] theorem subst_productBudget {l : ℕ} (σ : Fin n → PTm l) (B D J : PTm n) :
    Syn.subst σ (productBudget B D J) = productBudget (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ J) :=
  by simp [productBudget,factorBudget,one]

theorem canonical_product (p J z s : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (normalizedProduct p J z s) :=
  product_canonical _ _ _

private theorem body_at (p J z s k : PTm n) : Γ ⊢[PRAAx]
    LeanProofs.IPRA.inst2 body k (data p J z s) ≐ normalizedFactor s (sineSample p (succ (monus J (succ k))) J z) := by
  have tail1 := snd_pair (Γ := Γ) p (pairT J (pairT z s))
  have tail2 := (congrSnd tail1).eqTrans (snd_pair _ _)
  simpa [body,LeanProofs.IPRA.inst2] using
    Prf.eqCongr (Γ := Γ) (normalizedFactor (var 3) (sineSample (var 0) (succ (monus (var 1) (succ (var 4))))
      (var 1) (var 2)) : PTm 5)
      (σ := ![fstT (data p J z s),fstT (sndT (data p J z s)),fstT (sndT (sndT (data p J z s))),
        sndT (sndT (sndT (data p J z s))),k])
      (σ' := ![p,J,z,s,k]) (fun i => by
        fin_cases i
        · exact fst_pair _ _
        · exact (congrFst tail1).eqTrans (fst_pair _ _)
        · exact (congrFst tail2).eqTrans (fst_pair _ _)
        · exact (congrSnd tail2).eqTrans (snd_pair _ _)
        · exact .eqRefl _)

theorem normalized_prefix_zero (p J z s : PTm n) : Γ ⊢[PRAAx] normalizedPrefix p J z s zero ≐ qone :=
  product_zero _ _

theorem normalized_prefix_succ (p J z s k : PTm n) :
    Γ ⊢[PRAAx] normalizedPrefix p J z s (succ k) ≐ qmul
      (normalizedFactor s (sineSample p (succ (monus J (succ k))) J z)) (normalizedPrefix p J z s k) :=
  (product_succ body k (data p J z s)).eqTrans
    ((qmul_congr (.eqRefl _) (body_at p J z s k)).eqTrans (qmul_commutative _ _))

theorem factor_bound (s r B D : PTm n) (hd : Γ ⊢[PRAAx] le one D)
    (hs : Γ ⊢[PRAAx] bounded s B one) (hr : Γ ⊢[PRAAx] lower r D) :
    Γ ⊢[PRAAx] bounded (normalizedFactor s r) (factorBudget B D) one := by
  let S := qmul s s
  let R := qmul r r
  have h2 := positive_product D D hd hd
  have low := product_lower r r one D one D hd hd hr hr
  have lowerR : Γ ⊢[PRAAx] lower R (D*D) :=
    name_lower R (one*one) (D*D) (positive_product _ _ (le_refl _) (le_refl _)) h2 low
  have inv := inverse_bound R (D*D) h2 lowerR
  have sq : Γ ⊢[PRAAx] bounded S (B*B) one :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
      (bounded_product _ _ _ _ _ _ (le_refl _) (le_refl _) hs hs)
  have prod : Γ ⊢[PRAAx] bounded (qmul S (reciprocal R)) ((B*B)*(D*D)) one :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
      (bounded_product _ _ _ _ _ _ (le_refl _) (le_refl _) sq inv)
  exact bound_congr (.eqRefl _) (by unfold factorBudget; ipra_ring) (by ipra_ring)
    (bounded_difference _ _ _ _ _ _ (le_refl _) (le_refl _) qone_bounded prod)

def prefixLaw (p J z s B D k : PTm n) : Fm PTm n := le k J ⟶
  (qmul (factors (roots p J z) J (naturalPoint (num 4)) k) (normalizedPrefix p J z s k) ≐
    factors (roots p J z) J (fromSine s) k) ⋏ bounded (normalizedPrefix p J z s k) (productBudget B D k) one

@[simp] theorem subst_prefixLaw {l : ℕ} (σ : Fin n → PTm l) (p J z s B D k : PTm n) :
    (prefixLaw p J z s B D k).subst σ =
      prefixLaw (Syn.subst σ p) (Syn.subst σ J) (Syn.subst σ z) (Syn.subst σ s)
        (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ k) := by
  simp [prefixLaw,fromSine,one]

private theorem prefix_zero (p J z s B D : PTm n) : Γ ⊢[PRAAx] prefixLaw p J z s B D zero := by
  refine .impI (.andI ?_ ?_)
  · exact (qmul_congr (factors_zero _ _ _) (normalized_prefix_zero _ _ _ _)).eqTrans
      ((qmul_one_right _ qone_canonical).eqTrans (factors_zero _ _ _).eqSymm)
  · exact bound_congr (normalized_prefix_zero _ _ _ _).eqSymm (pw_zero _).eqSymm (.eqRefl _) qone_bounded

private theorem prefix_succ (p J z s B D k : PTm n) (hd : Γ ⊢[PRAAx] le one D)
    (hs : Γ ⊢[PRAAx] bounded s B one) (hm : Γ ⊢[PRAAx] sineMargins p J z D)
    (previous : Γ ⊢[PRAAx] prefixLaw p J z s B D k) : Γ ⊢[PRAAx] prefixLaw p J z s B D (succ k) := by
  refine .impI ?_
  let Δ := le (succ k) J :: Γ
  let r := monus J (succ k)
  let a := sineSample p (succ r) J z
  let R := roots p J z
  let y := fromSine s
  let four := naturalPoint (num 4 : PTm n)
  have step : Δ ⊢[PRAAx] lt k J := Prf.hyp0
  have rj : Δ ⊢[PRAAx] lt r J := le_of_eq_add (d := k) (AnalyticNumberTheory.Totatives.split_lt step)
  have root := roots_at p J z r rj
  have hm' := sine_margin_at p J z D r hm.wk rj
  have old := Prf.impE previous.wk (le_of_lt step)
  have sameY := (factors_succ R J y k).eqTrans (qmul_congr (qsub_congr (.eqRefl _) root) (.eqRefl _))
  have sameFour := (factors_succ R J four k).eqTrans (qmul_congr (qsub_congr (.eqRefl _) root) (.eqRefl _))
  have value := (qmul_congr sameFour (normalized_prefix_succ p J z s k)).eqTrans
    ((qmul_shuffle _ _ _ _).eqTrans
      ((qmul_congr (root_factor_normalization s a D hd.wk hm') old.andE₁).eqTrans sameY.eqSymm))
  have rate : Δ ⊢[PRAAx] productBudget B D k*factorBudget B D ≐ productBudget B D (succ k) :=
    (pw_succ _ _).eqSymm
  have norm : Δ ⊢[PRAAx] bounded (normalizedPrefix p J z s (succ k)) (productBudget B D (succ k)) one :=
    bound_congr (normalized_prefix_succ p J z s k).eqSymm
      ((mul_comm _ _).eqTrans rate) (by ipra_ring)
      (bounded_product _ _ _ _ _ _ (le_refl _) (le_refl _) (factor_bound s a B D hd.wk hs.wk hm') old.andE₂)
  exact .andI value norm

theorem prefix_control (p J z s B D k : PTm n) (hd : Γ ⊢[PRAAx] le one D)
    (hs : Γ ⊢[PRAAx] bounded s B one) (hm : Γ ⊢[PRAAx] sineMargins p J z D) :
    Γ ⊢[PRAAx] prefixLaw p J z s B D k := by
  have hd' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift D) := by simpa [Fm.shift,Syn.shift,one] using hd.shift
  have hs' : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift s) (Syn.shift B) one :=
    by simpa [Fm.shift,Syn.shift,one] using hs.shift
  have hm' : Γ.map Fm.shift ⊢[PRAAx] sineMargins (Syn.shift p) (Syn.shift J) (Syn.shift z) (Syn.shift D) :=
    by simpa [Fm.shift,Syn.shift] using hm.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift p) (Syn.shift J) (Syn.shift z)
      (Syn.shift s) (Syn.shift B) (Syn.shift D) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial,le_QF _ _⟩ ?_ ?_
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using prefix_zero (Γ := Γ) p J z s B D
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        prefix_succ _ _ _ _ _ _ (var 0) hd'.wk hs'.wk hm'.wk Prf.hyp0
  simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

theorem folded_identity (p J z s B D : PTm n) (hd : Γ ⊢[PRAAx] le one D) (hs : Γ ⊢[PRAAx] bounded s B one)
    (hm : Γ ⊢[PRAAx] sineMargins p J z D) :
    Γ ⊢[PRAAx] qmul (product (roots p J z) J (naturalPoint (num 4))) (normalizedProduct p J z s) ≐
      product (roots p J z) J (fromSine s) :=
  (Prf.impE (prefix_control p J z s B D J hd hs hm) (le_refl _)).andE₁

theorem product_bound (p J z s B D : PTm n) (hd : Γ ⊢[PRAAx] le one D) (hs : Γ ⊢[PRAAx] bounded s B one)
    (hm : Γ ⊢[PRAAx] sineMargins p J z D) :
    Γ ⊢[PRAAx] bounded (normalizedProduct p J z s) (productBudget B D J) one :=
  (Prf.impE (prefix_control p J z s B D J hd hs hm) (le_refl _)).andE₂

theorem actual_normalized_sample_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 5) ⟶ (bounded (var 3) (var 4) one ⋏ sineMargins (var 0) (var 1) (var 2) (var 5)) ⟶
      qmul (product (roots (var 0) (var 1) (var 2)) (var 1) (naturalPoint (num 4)))
        (normalizedProduct (var 0) (var 1) (var 2) (var 3)) ≐
          product (roots (var 0) (var 1) (var 2)) (var 1) (fromSine (var 3))) :=
  closeUniv 6 (.impI (.impI (folded_identity _ _ _ _ _ _ Prf.hyp1 Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianSineNormalizedSampleProduct
