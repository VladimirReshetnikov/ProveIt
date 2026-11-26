import IPRADerivations.Analysis.Barnes.HeadProducts.GaussianBarnesCanonicalFactor
import IPRADerivations.Analysis.Names.FiniteOperations.Products.GaussianNamedFiniteProductFamilyAppend
import IPRADerivations.Analysis.Gamma.Integrals.GaussianGammaCompactCutoffAlignment
import IPRADerivations.Analysis.Gamma.Integrals.GaussianGammaCompactCutoffSplit

/-!
# Actual finite Barnes canonical products

A finite name runs the original factor evaluator at each index
(N+1,\ldots,N+r). The same program gives a head when (N=0) and
a tail segment at any other internal starting index.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHead

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedFiniteProductFamily (rowF row_at regularRows productData family_product_regular)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalFactor.nameF
local notation "factorData" => GaussianBarnesCanonicalFactor.data

def source (z R B : PTm n) : Fm PTm n :=
  le one B ⋏ ComplexLogarithmRemainder.bounded z (R*B)

def parameters (z R B N : PTm n) : PTm n := pairT z (pairT R (pairT B N))

def body : PTm 2 :=
  let x := var 1
  factorData (fstT x) (fstT (sndT x)) (fstT (sndT (sndT x))) (succ (sndT (sndT (sndT x))+var 0))

def nameF : PR 2 := GaussianNamedFiniteProductName.nameF (rowF F body)

def data (z R B N r : PTm n) : PTm n := productData F body r (parameters z R B N)

def headData (z R B r : PTm n) : PTm n := data z R B zero r

def cap (R N r : PTm n) : PTm n :=
  GaussianNamedFiniteProduct.radius (GaussianBarnesCanonicalFactor.cap R (N+r)) r

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B : PTm n) :
    (source z R B).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [source,one]

@[simp] theorem subst_parameters {m : ℕ} (σ : Fin n → PTm m) (z R B N : PTm n) :
    Syn.subst σ (parameters z R B N) =
      parameters (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [parameters]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B N r : PTm n) :
    Syn.subst σ (data z R B N r) =
      data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) := by
  simp [data,productData,GaussianNamedFiniteProductFamily.radius,one]

@[simp] theorem subst_cap {m : ℕ} (σ : Fin n → PTm m) (R N r : PTm n) :
    Syn.subst σ (cap R N r) = cap (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ r) := by simp [cap]

theorem body_at (i z R B N : PTm n) : Γ ⊢[PRAAx]
    inst2 body i (parameters z R B N) ≐ factorData z R B (succ (N+i)) := by
  let x := parameters z R B N
  let t : PTm 5 := factorData (var 1) (var 2) (var 3) (succ (var 4+var 0))
  have tail := snd_pair (Γ := Γ) z (pairT R (pairT B N))
  have tail₂ := (congrSnd tail).eqTrans (snd_pair R (pairT B N))
  have read := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) t
    (σ := ![i,fstT x,fstT (sndT x),fstT (sndT (sndT x)),sndT (sndT (sndT x))])
    (σ' := ![i,z,R,B,N])
    (fun j => by
      fin_cases j
      · exact .eqRefl i
      · exact fst_pair _ _
      · exact (congrFst tail).eqTrans (fst_pair _ _)
      · exact (congrFst tail₂).eqTrans (fst_pair _ _)
      · exact (congrSnd tail₂).eqTrans (snd_pair _ _))
  simpa only [body,inst2,t,x,GaussianBarnesCanonicalFactor.subst_data,subst_fstT,subst_sndT,
    PTm.subst_add,PTm.subst_succ,Syn.subst_var,Matrix.cons_val] using read

theorem factor_at (p i z R B N : PTm n) : Γ ⊢[PRAAx]
    ap3 (rowF F body) p i (parameters z R B N) ≐ ap2 F p (factorData z R B (succ (N+i))) :=
  (row_at F body p i _).eqTrans (congrAp2 F (.eqRefl p) (body_at i z R B N))

theorem rows_regular (z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] regularRows F body r (parameters z R B N) := by
  refine .allI (.impI ?_)
  let sh (x : PTm n) := Syn.shift x
  let Δ := lt (var 0) (sh r) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.wk
  have rr := GaussianBarnesCanonicalFactor.regular (sh z) (sh R) (sh B) (succ (sh N+var 0))
    (.andI hs.andE₁ (.andI (zero_lt_succ _) hs.andE₂))
  simpa only [Syn.shift,sh,Δ,subst_parameters] using
    GaussianGammaCompactCutoffSplit.point_data_congr F _ _
      (body_at (var 0) (sh z) (sh R) (sh B) (sh N)).eqSymm rr

theorem regular (z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B N r) :=
  family_product_regular F body r _ (rows_regular z R B N r h)

theorem sample_at (p z R B N r : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data z R B N r) ≐ GaussianNamedFiniteProduct.sample (rowF F body)
      (GaussianNamedFiniteProductName.clock r (GaussianNamedFiniteProductFamily.radius F body r (parameters z R B N)) one p)
      r (parameters z R B N) :=
  GaussianNamedFiniteProductName.name_at (rowF F body) p r _ one _

theorem sample_bound (p z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data z R B N r)) (cap R N r) one := by
  let s := GaussianNamedFiniteProductName.clock r (GaussianNamedFiniteProductFamily.radius F body r (parameters z R B N)) one p
  let A := GaussianBarnesCanonicalFactor.cap R (N+r)
  have rows : Γ ⊢[PRAAx] GaussianNamedFiniteProduct.rowBoundsAt (rowF F body) s r A (parameters z R B N) := by
    refine .allI (.impI ?_)
    let sh (x : PTm n) := Syn.shift x
    let Δ := lt (var 0) (sh r) :: Γ.map Fm.shift
    let m := succ (sh N+var 0)
    have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.wk
    have hi : Δ ⊢[PRAAx] le m (sh N+sh r) :=
      le_congr ((add_comm (succ (var 0)) (sh N)).eqTrans (add_succ (sh N) (var 0)))
        (add_comm (sh r) (sh N)) (add_le_add_right (sh N) Prf.hyp0)
    have order : Δ ⊢[PRAAx] le (GaussianBarnesCanonicalFactor.cap (sh R) m)
        (GaussianBarnesCanonicalFactor.cap (sh R) (sh N+sh r)) :=
      mul_le_mul_right _ (GaussianFactorBudget.power_monotone_length _ _ _ (le_add_left one (sh R)) hi)
    have bound := GaussianBarnesCanonicalFactor.sample_bound (sh s) (sh z) (sh R) (sh B) m
      (.andI hs.andE₁ (.andI (zero_lt_succ _) hs.andE₂))
    have e := GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
      (mul_le_mul_right one order) bound
    simpa only [Syn.shift,sh,Δ,A,GaussianBarnesCanonicalFactor.subst_cap,PTm.subst_add,subst_parameters] using
      bound_congr (factor_at (sh s) (var 0) (sh z) (sh R) (sh B) (sh N)).eqSymm (.eqRefl _) (.eqRefl _) e
  exact bound_congr (sample_at p z R B N r).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianNamedFiniteProduct.sample_bound (rowF F body) s r A (parameters z R B N) rows)

theorem empty (z R B N : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent nameF GaussianNameRingLaws.oneF (data z R B N zero) (parameters z R B N) :=
  GaussianNamedFiniteProductAppend.empty_cross (rowF F body) _ one _

theorem append_cross (z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] crossEquivalent nameF (multiplyF nameF F) (data z R B N (succ r))
      (multiplyData nameF F (data z R B N r) (factorData z R B (succ (N+r)))) := by
  let x := parameters z R B N
  have e := GaussianNamedFiniteProductFamilyAppend.family_append_cross F body r x (rows_regular z R B N (succ r) h)
  have next : Γ ⊢[PRAAx] multiplyData nameF F (data z R B N r) (inst2 body r x) ≐
      multiplyData nameF F (data z R B N r) (factorData z R B (succ (N+r))) := by
    simpa only [GaussianNameArithmetic.subst_multiplyData,Syn.subst_var,Matrix.cons_val] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (multiplyData nameF F (var 0) (var 1) : PTm 2)
        (σ := ![data z R B N r,inst2 body r x]) (σ' := ![data z R B N r,factorData z R B (succ (N+r))])
        (fun j => by
          fin_cases j
          · exact .eqRefl _
          · exact body_at r z R B N)
  exact GaussianGammaCompactCutoffAlignment.cross_data_congr nameF (multiplyF nameF F) _ _ _ _
    (.eqRefl _) next e

theorem actual_original_Barnes_finite_head_regular_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source (var 0) (var 1) (var 2) ⟶ pointCN nameF (headData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (regular _ _ _ zero _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHead
