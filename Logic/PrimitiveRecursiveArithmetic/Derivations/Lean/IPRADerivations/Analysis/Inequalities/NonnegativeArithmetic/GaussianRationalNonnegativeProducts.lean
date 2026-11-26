import IPRADerivations.Analysis.Names.FiniteOperations.Products.GaussianNamedFiniteProduct
import IPRADerivations.Analysis.RationalArithmetic.Embeddings.RationalGaussianEmbedding
import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalRepresentedUpper

/-!
# Finite products of nonnegative Gaussian real-axis observations

The quantifier-free code predicate records a vanishing imaginary
coordinate and a nonnegative real coordinate. The actual rational
multiplication preserves it, including the empty finite product.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalNonnegativeProducts

open_ipra
open ComplexLogarithmRemainder (re im oneCode)
open GaussianRationalHorner (canonical qadd qadd_represents qadd_canonical qmul qmul_represents qmul_canonical
  ofGaussian_represents scalar_congr positive_product)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRootAlgebra (re_one im_one re_mul im_mul re_add im_add)
open GaussianRationalReciprocal (qone)
open GaussianRationalSyntheticDivision (qone_canonical)
open RationalRepresentedUpper (left right to_signed from_signed)
open RationalGaussianEmbedding (scalarZero scalar_zero_represents)
open RationalSupMetric (denominatorOf)
open RationalValueBounds (upper upper_of_order)
open RationalArgmin (rationalLE)
open GaussianNamedFiniteProduct (sample sample_zero sample_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def nonnegative (q : PTm n) : Fm PTm n := rationalLE scalarZero (fstT q) ⋏ sndT q ≐ scalarZero

ipra_subst nonnegative

theorem congr {q r : PTm n} (h : Γ ⊢[PRAAx] q ≐ r) (hq : Γ ⊢[PRAAx] nonnegative q) :
    Γ ⊢[PRAAx] nonnegative r :=
  .andI (RationalArgmin.rationalLE_congr (.eqRefl _) (congrFst h) hq.andE₁)
    ((congrSnd h).eqSymm.eqTrans hq.andE₂)

private def positiveSlack (a : ZT n) : PTm n := monus (a.pos+(ZT.ofNat (zero : PTm n)).neg) ((ZT.ofNat zero).pos+a.neg)

private theorem signed_real (q a E : PTm n)
    (hr : Γ ⊢[PRAAx] GaussianRationalHorner.represents q a E)
    (h : Γ ⊢[PRAAx] rationalLE scalarZero (fstT q)) :
    Γ ⊢[PRAAx] zle (ZT.ofNat zero) (re a) := by
  let z := re a
  let L := left (ZT.ofNat zero) E one
  let R := right z one E zero one
  let w := monus (R.pos+L.neg) (L.pos+R.neg)
  have sg : Γ ⊢[PRAAx] zle L R :=
    to_signed _ _ _ _ one E zero one (scalar_zero_represents one) hr.andE₁
      (upper_of_order scalarZero (fstT q) zero one h)
  have e := zle_toZ sg
  change ZT.toZ Γ L+𝔞 w = ZT.toZ Γ R at e
  apply zle_of_toZ w
  simp only [L,R,left,right,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,IPRA.Q.mk_mul,map_mul] at e ⊢
  dsimp only [z] at e
  simp only [IPRA.Q.mk_zero,IPRA.Q.mk_one,map_zero,map_one] at e ⊢
  linear_combination e

private theorem signed_imaginary (q a E : PTm n)
    (hr : Γ ⊢[PRAAx] GaussianRationalHorner.represents q a E) (h : Γ ⊢[PRAAx] sndT q ≐ scalarZero) :
    Γ ⊢[PRAAx] ZT.eq (im a) (ZT.ofNat zero) := by
  let D := denominatorOf (sndT q)
  have r := scalar_congr h.eqSymm (.eqRefl _) (.eqRefl _) (scalar_zero_represents E)
  apply RationalNormalForm.positive_integer_cancel D _ _ (RationalArgmin.denominator_positive (sndT q))
  apply ZT.derive
  have e := ZT.toZ_eq hr.andE₂
  have er := ZT.toZ_eq r
  simp only [ZT.toZ_mul,ZT.toZ_ofNat] at e er ⊢
  dsimp only [D]
  linear_combination e-er

private theorem from_representation (q a E : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hc : Γ ⊢[PRAAx] canonical q) (hr : Γ ⊢[PRAAx] GaussianRationalHorner.represents q a E)
    (hp : Γ ⊢[PRAAx] zle (ZT.ofNat zero) (re a)) (hz : Γ ⊢[PRAAx] ZT.eq (im a) (ZT.ofNat zero)) :
    Γ ⊢[PRAAx] nonnegative q := by
  let z := re a
  let w := positiveSlack z
  have hs : Γ ⊢[PRAAx] zle (left (ZT.ofNat zero) E one) (right z one E zero one) := by
    apply zle_of_toZ w
    have v := zle_toZ hp
    change ZT.toZ Γ (ZT.ofNat zero)+𝔞 w = ZT.toZ Γ z at v
    simp only [left,right,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,IPRA.Q.mk_mul,map_mul] at v ⊢
    simp only [IPRA.Q.mk_zero,IPRA.Q.mk_one,map_zero,map_one] at v ⊢
    linear_combination v
  have r := from_signed scalarZero (fstT q) _ z one E zero one (le_refl one) hE
    (scalar_zero_represents one) hr.andE₁ hs
  have hreal : Γ ⊢[PRAAx] rationalLE scalarZero (fstT q) := by
    unfold rationalLE RationalArgmin.left
    exact le_congr (by unfold RationalValueBounds.crossLeft; ipra_ring)
      (by unfold RationalValueBounds.crossLeft; ipra_ring) r
  have him : Γ ⊢[PRAAx] sndT q ≐ scalarZero := by
    apply RationalFiniteSum.canonical_equal _ _ _ _ _ one hc.andE₂.andE₂
      (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
      (scalar_congr (.eqRefl _) hz (.eqRefl _) hr.andE₂) (scalar_zero_represents one) hE (le_refl one)
    apply ZT.derive
    simp [ZT.toZ_mul,ZT.toZ_ofNat,IPRA.Q.mk_zero,map_zero]
  exact .andI hreal him

theorem nonnegative_one : Γ ⊢[PRAAx] nonnegative (qone : PTm n) := by
  apply from_representation _ oneCode one (le_refl one) qone_canonical (ofGaussian_represents _ _ (le_refl one))
  · apply zle_of_toZ one
    simp only [re_one,ZT.toZ_ofNat]
    ipra_simps
    ring
  · apply ZT.derive
    simp [im_one,ZT.toZ_ofNat,IPRA.Q.mk_zero,map_zero]

theorem nonnegative_mul (q r : PTm n) (hq : Γ ⊢[PRAAx] nonnegative q) (hr : Γ ⊢[PRAAx] nonnegative r) :
    Γ ⊢[PRAAx] nonnegative (qmul q r) := by
  let a := rawGaussian q
  let b := rawGaussian r
  let E := rawDen q
  let F := rawDen r
  let MA := positiveSlack (re a)
  let MB := positiveSlack (re b)
  have hE := raw_den_positive (Γ := Γ) q
  have hF := raw_den_positive (Γ := Γ) r
  have qa := raw_represents (Γ := Γ) q
  have rb := raw_represents (Γ := Γ) r
  have aRe : ZT.toZ Γ (ZT.ofNat zero)+𝔞 MA = ZT.toZ Γ (re a) := zle_toZ (signed_real q a E qa hq.andE₁)
  have bRe : ZT.toZ Γ (ZT.ofNat zero)+𝔞 MB = ZT.toZ Γ (re b) := zle_toZ (signed_real r b F rb hr.andE₁)
  have aIm := ZT.toZ_eq (signed_imaginary q a E qa hq.andE₂)
  have bIm := ZT.toZ_eq (signed_imaginary r b F rb hr.andE₂)
  apply from_representation _ _ (E*F) (positive_product _ _ hE hF) (qmul_canonical _ _)
    (qmul_represents _ _ _ _ _ _ hE hF qa rb)
  · apply zle_of_toZ (MA*MB)
    rw [re_mul,aIm,bIm,← aRe,← bRe]
    simp only [ZT.toZ_ofNat,IPRA.Q.mk_mul,map_mul]
    ipra_simps
    ring
  · apply ZT.derive
    rw [im_mul,aIm,bIm]
    simp [ZT.toZ_ofNat,IPRA.Q.mk_zero,map_zero]

theorem nonnegative_double (q : PTm n) (hq : Γ ⊢[PRAAx] nonnegative q) :
    Γ ⊢[PRAAx] nonnegative (qadd q q) := by
  let a := rawGaussian q
  let E := rawDen q
  let T := positiveSlack (re a)
  have hE := raw_den_positive (Γ := Γ) q
  have qa := raw_represents (Γ := Γ) q
  have aRe : ZT.toZ Γ (ZT.ofNat zero)+𝔞 T = ZT.toZ Γ (re a) := zle_toZ (signed_real q a E qa hq.andE₁)
  apply from_representation _ _ E hE (qadd_canonical _ _) (qadd_represents _ _ _ _ _ hE qa qa)
  · apply zle_of_toZ (T+T)
    rw [re_add,← aRe]
    simp only [ZT.toZ_ofNat,IPRA.Q.mk_add,map_add]
    ipra_simps
    ring
  · apply ZT.derive
    rw [im_add,ZT.toZ_eq (signed_imaginary q a E qa hq.andE₂)]
    simp [ZT.toZ_ofNat,IPRA.Q.mk_zero,map_zero]

def nonnegativeRows (f : PR 3) (p N x : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift N) ⟶ nonnegative (ap3 f (Syn.shift p) (var 0) (Syn.shift x)))

ipra_subst nonnegativeRows [Syn.subst_shift, Syn.shift_subst]

theorem row_at (f : PR 3) (p N x i : PTm n)
    (h : Γ ⊢[PRAAx] nonnegativeRows f p N x) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] nonnegative (ap3 f p i x) := by
  have e : Γ ⊢[PRAAx] lt i N ⟶ nonnegative (ap3 f p i x) := by
    simpa [nonnegativeRows] using h.allE i
  exact .impE e hi

private def prefixLaw (f : PR 3) (p N x i : PTm n) : Fm PTm n :=
  le i N ⟶ nonnegative (sample f p i x)

@[simp] private theorem subst_prefixLaw {L : ℕ} (σ : Fin n → PTm L) (f : PR 3) (p N x i : PTm n) :
    (prefixLaw f p N x i).subst σ =
      prefixLaw f (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ i) := by simp [prefixLaw]

theorem sample_nonnegative (f : PR 3) (p N x : PTm n) (h : Γ ⊢[PRAAx] nonnegativeRows f p N x) :
    Γ ⊢[PRAAx] nonnegative (sample f p N x) := by
  have h' : Γ.map Fm.shift ⊢[PRAAx] nonnegativeRows f (Syn.shift p) (Syn.shift N) (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw f (Syn.shift p) (Syn.shift N) (Syn.shift x) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,⟨le_QF _ _,trivial⟩⟩) [subst_prefixLaw]
    · exact .impI (congr (sample_zero f p x).eqSymm nonnegative_one).wk
    · refine .impI ?_
      let I : PTm (n+1) := var 0
      let P := Syn.shift p
      let M := Syn.shift N
      let X := Syn.shift x
      let Δ := le (succ I) M :: prefixLaw f P M X I :: Γ.map Fm.shift
      have hi : Δ ⊢[PRAAx] lt I M := Prf.hyp0
      have ih : Δ ⊢[PRAAx] nonnegative (sample f P I X) := Prf.impE Prf.hyp1 (le_of_lt hi)
      exact congr (sample_succ f (Syn.shift p) (var 0) (Syn.shift x)).eqSymm
        (nonnegative_mul _ _ ih (row_at f _ _ _ _ h'.wk.wk Prf.hyp0))
  have rule : Γ ⊢[PRAAx] prefixLaw f p N x N := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  exact .impE rule (le_refl N)

end LeanProofs.IPRA.Analysis.GaussianRationalNonnegativeProducts
