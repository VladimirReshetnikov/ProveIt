import IPRADerivations.Analysis.Names.FiniteOperations.Products.GaussianNamedFiniteProductName

/-!
# Multiplication of finite families of Gaussian names

The original product fold commutes with rowwise products. Both row
families may have their own regularity bounds and original query
clocks. The resulting named product respects the original rational
fold, including at internal count zero.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNamedFiniteProductAlgebra

open_ipra
open GaussianNamedFiniteProductName (shift_row_bounds shift_row_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameArithmetic (multiplyF multiplyData multiplyRawF multiplyModulus multiply_raw_at
  multiply_regular product_distance)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedFiniteProduct (sample sample_zero sample_succ sample_bound radius rowBoundsAt rowDistance
  row_bound_at row_distance_at)
open GaussianNamedFiniteProductName (nameF data modulus rawF rawData raw_at raw_regular name_regular name_bound
  rowBounds rowRegular bounds_at regular_rows_at)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPowerAlgebra (qmul_shuffle)
open GaussianRationalReciprocal (bounded_product bound_congr qone)
open GaussianRationalSyntheticDivision (qmul_congr qone_canonical)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rowProductBody (f g : PR 3) : PTm 3 :=
  qmul (ap3 f (var 0) (var 1) (fstT (var 2))) (ap3 g (var 0) (var 1) (sndT (var 2)))

def rowProduct (f g : PR 3) : PR 3 := PTm.toPR (rowProductBody f g)

theorem row_at (f g : PR 3) (p i x y : PTm n) : Γ ⊢[PRAAx]
    ap3 (rowProduct f g) p i (pairT x y) ≐ qmul (ap3 f p i x) (ap3 g p i y) := by
  have read : Γ ⊢[PRAAx] ap3 (rowProduct f g) p i (pairT x y) ≐
      qmul (ap3 f p i (fstT (pairT x y))) (ap3 g p i (sndT (pairT x y))) := by
    change Γ ⊢[PRAAx] PTm.app (rowProduct f g) ![p,i,pairT x y] ≐
      qmul (ap3 f p i (fstT (pairT x y))) (ap3 g p i (sndT (pairT x y)))
    simpa only [rowProduct,rowProductBody,GaussianRationalHorner.subst_qmul,subst_ap3,
      subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (rowProductBody f g) ![p,i,pairT x y]
  exact read.eqTrans (qmul_congr (congrAp3 f (.eqRefl _) (.eqRefl _) (fst_pair x y))
    (congrAp3 g (.eqRefl _) (.eqRefl _) (snd_pair x y)))

def sampleLaw (f g : PR 3) (p N x y : PTm n) : Fm PTm n :=
  sample (rowProduct f g) p N (pairT x y) ≐ qmul (sample f p N x) (sample g p N y)

ipra_subst sampleLaw

theorem sample_product (f g : PR 3) (p N x y : PTm n) : Γ ⊢[PRAAx] sampleLaw f g p N x y := by
  have all : Γ ⊢[PRAAx] .all (sampleLaw f g (Syn.shift p) (var 0) (Syn.shift x) (Syn.shift y)) := by
    ipra_qfind [subst_sampleLaw]
    · exact (sample_zero (rowProduct f g) p (pairT x y)).eqTrans
        ((qmul_congr (sample_zero f p x) (sample_zero g p y)).eqTrans
          (GaussianReciprocalHorner.qmul_one_right qone qone_canonical)).eqSymm
    · exact (sample_succ (rowProduct f g) _ _ _).eqTrans
        ((qmul_congr Prf.hyp0 (row_at f g _ _ _ _)).eqTrans
          ((qmul_shuffle _ _ _ _).eqTrans
            (qmul_congr (sample_succ f _ _ _).eqSymm (sample_succ g _ _ _).eqSymm)))
  simpa only [subst_sampleLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem bounded_rows_at (f g : PR 3) (p N R S x y : PTm n) (hf : Γ ⊢[PRAAx] rowBoundsAt f p N R x)
    (hg : Γ ⊢[PRAAx] rowBoundsAt g p N S y) :
    Γ ⊢[PRAAx] rowBoundsAt (rowProduct f g) p N (R*S) (pairT x y) := by
  refine .allI (.impI ?_)
  let sh := fun t : PTm n => Syn.shift t
  let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
  have hF : Δ ⊢[PRAAx] rowBoundsAt f (sh p) (sh N) (sh R) (sh x) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using hf.shift.wk
  have hG : Δ ⊢[PRAAx] rowBoundsAt g (sh p) (sh N) (sh S) (sh y) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using hg.shift.wk
  have a := row_bound_at f (sh p) (sh N) (sh R) (sh x) (var 0) hF Prf.hyp0
  have b := row_bound_at g (sh p) (sh N) (sh S) (sh y) (var 0) hG Prf.hyp0
  simpa [rowBoundsAt,Syn.shift,sh,Δ,one] using
    bound_congr (row_at f g (sh p) (var 0) (sh x) (sh y)).eqSymm (.eqRefl _) (one_mul one)
      (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) a b)

theorem product_row_bounds (f g : PR 3) (N R S x y : PTm n) (hf : Γ ⊢[PRAAx] rowBounds f N R x)
    (hg : Γ ⊢[PRAAx] rowBounds g N S y) :
    Γ ⊢[PRAAx] rowBounds (rowProduct f g) N (R*S) (pairT x y) := by
  refine .allI ?_
  let sh := fun t : PTm n => Syn.shift t
  let Δ := Γ.map Fm.shift
  have hF := shift_row_bounds hf
  have hG := shift_row_bounds hg
  simpa [rowBounds,Syn.shift,sh,Δ] using bounded_rows_at f g (var 0) (sh N) (sh R) (sh S) (sh x) (sh y)
    (bounds_at _ _ _ _ _ hF) (bounds_at _ _ _ _ _ hG)

theorem product_rows_distance (f g : PR 3) (p q N R S A B D E x y : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hE : Γ ⊢[PRAAx] A*S+R*B ≐ E)
    (hf : Γ ⊢[PRAAx] rowBoundsAt f q N R x) (hg : Γ ⊢[PRAAx] rowBoundsAt g p N S y)
    (df : Γ ⊢[PRAAx] rowDistance f f p q N A D x x) (dg : Γ ⊢[PRAAx] rowDistance g g p q N B D y y) :
    Γ ⊢[PRAAx] rowDistance (rowProduct f g) (rowProduct f g) p q N E D (pairT x y) (pairT x y) := by
  refine .allI (.impI ?_)
  let sh := fun t : PTm n => Syn.shift t
  let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
  have hD' : Δ ⊢[PRAAx] le one (sh D) := by simpa [Fm.shift,Syn.shift,sh,Δ,one] using hD.shift.wk
  have hE' : Δ ⊢[PRAAx] sh A*sh S+sh R*sh B ≐ sh E := by simpa [Fm.shift,Syn.shift,sh,Δ] using hE.shift.wk
  have hF : Δ ⊢[PRAAx] rowBoundsAt f (sh q) (sh N) (sh R) (sh x) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using hf.shift.wk
  have hG : Δ ⊢[PRAAx] rowBoundsAt g (sh p) (sh N) (sh S) (sh y) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using hg.shift.wk
  have dF : Δ ⊢[PRAAx] rowDistance f f (sh p) (sh q) (sh N) (sh A) (sh D) (sh x) (sh x) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using df.shift.wk
  have dG : Δ ⊢[PRAAx] rowDistance g g (sh p) (sh q) (sh N) (sh B) (sh D) (sh y) (sh y) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using dg.shift.wk
  have a := row_distance_at f f (sh p) (sh q) (sh N) (sh A) (sh D) (sh x) (sh x) (var 0) dF Prf.hyp0
  have b := row_distance_at g g (sh p) (sh q) (sh N) (sh B) (sh D) (sh y) (sh y) (var 0) dG Prf.hyp0
  have u := row_bound_at g (sh p) (sh N) (sh S) (sh y) (var 0) hG Prf.hyp0
  have v := row_bound_at f (sh q) (sh N) (sh R) (sh x) (var 0) hF Prf.hyp0
  simpa [rowDistance,Syn.shift,sh,Δ] using distance_congr (row_at f g (sh p) (var 0) (sh x) (sh y)).eqSymm
    (row_at f g (sh q) (var 0) (sh x) (sh y)).eqSymm hE' (.eqRefl _)
    (product_distance _ _ _ _ _ _ _ _ _ hD' a b u v)

theorem product_row_regular (f g : PR 3) (N R S L M x y : PTm n) (hf : Γ ⊢[PRAAx] rowBounds f N R x)
    (hg : Γ ⊢[PRAAx] rowBounds g N S y) (df : Γ ⊢[PRAAx] rowRegular f N L x)
    (dg : Γ ⊢[PRAAx] rowRegular g N M y) :
    Γ ⊢[PRAAx] rowRegular (rowProduct f g) N (L*S+R*M) (pairT x y) := by
  refine .allI (.allI ?_)
  let sh := fun t : PTm n => Syn.shift (Syn.shift t)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  let D := unit p*unit q
  let c := unit p+unit q
  have hF := shift_row_bounds (shift_row_bounds hf)
  have hG := shift_row_bounds (shift_row_bounds hg)
  have dF := shift_row_regular (shift_row_regular df)
  have dG := shift_row_regular (shift_row_regular dg)
  have d := product_rows_distance f g p q (sh N) (sh R) (sh S) (sh L*c) (sh M*c) D
    ((sh L*sh S+sh R*sh M)*c) (sh x) (sh y)
    (positive_product _ _ (unit_positive p) (unit_positive q)) (by ipra_ring)
    (bounds_at _ _ _ _ _ hF) (bounds_at _ _ _ _ _ hG)
    (regular_rows_at _ _ _ _ _ _ dF) (regular_rows_at _ _ _ _ _ _ dG)
  simpa [rowRegular,Syn.shift,sh,Δ,p,q,D,c] using d

def productBudget (N R S L M : PTm n) : PTm n :=
  (modulus N R L+one)*radius S N+radius R N*(modulus N S M+one)

ipra_subst productBudget [one]

theorem diagonal_product_error (f g : PR 3) (p N R S L M x y : PTm n)
    (hf : Γ ⊢[PRAAx] rowBounds f N R x) (hg : Γ ⊢[PRAAx] rowBounds g N S y)
    (df : Γ ⊢[PRAAx] rowRegular f N L x) (dg : Γ ⊢[PRAAx] rowRegular g N M y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (rawF (rowProduct f g)) p (rawData N (pairT x y)))
      (ap2 (multiplyRawF (nameF f) (nameF g)) p
        (GaussianNameArithmetic.data (data N R L x) (data N S M y))) (productBudget N R S L M) (unit p) := by
  let h := unit_positive (Γ := Γ) p
  let u := GaussianNameRingLaws.normalized_to_sample (rawF f) (modulus N R L) (rawData N x) p
    (raw_regular f N R L x hf df)
  let v := GaussianNameRingLaws.normalized_to_sample (rawF g) (modulus N S M) (rawData N y) p
    (raw_regular g N S M y hg dg)
  have a := distance_symmetric _ _ _ _ h u
  have b := distance_symmetric _ _ _ _ h v
  have ru := bound_congr (raw_at g p N y).eqSymm (.eqRefl _) (.eqRefl _)
    (sample_bound g p N S y (bounds_at g p N S y hg))
  have rv := name_bound f p N R L x hf
  have left := (raw_at (Γ := Γ) (rowProduct f g) p N (pairT x y)).eqTrans
    ((sample_product f g p N x y).eqTrans (qmul_congr (raw_at f p N x).eqSymm (raw_at g p N y).eqSymm))
  have right := multiply_raw_at (Γ := Γ) (nameF f) (nameF g) p (data N R L x) (data N S M y)
  exact distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _)
    (product_distance _ _ _ _ _ _ _ _ _ h a b ru rv)

theorem named_product (f g : PR 3) (N R S L M x y : PTm n)
    (hf : Γ ⊢[PRAAx] rowBounds f N R x) (hg : Γ ⊢[PRAAx] rowBounds g N S y)
    (df : Γ ⊢[PRAAx] rowRegular f N L x) (dg : Γ ⊢[PRAAx] rowRegular g N M y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF (rowProduct f g)) (multiplyF (nameF f) (nameF g))
      (data N (R*S) (L*S+R*M) (pairT x y)) (multiplyData (nameF f) (nameF g) (data N R L x) (data N S M y)) := by
  let X := data N R L x
  let Y := data N S M y
  have left := raw_regular (rowProduct f g) N (R*S) (L*S+R*M) (pairT x y)
    (product_row_bounds f g N R S x y hf hg) (product_row_regular f g N R S L M x y hf hg df dg)
  have right := multiply_regular (nameF f) (nameF g) X Y
    (name_regular f N R L x hf df) (name_regular g N S M y hg dg)
  refine GaussianValueNormalizerExtensionality.normalized_names_equivalent _ _ _ _ _ _
    (productBudget N R S L M) left right (.allI ?_)
  let sh := fun t : PTm n => Syn.shift t
  let Δ := Γ.map Fm.shift
  have hF : Δ ⊢[PRAAx] rowBounds f (sh N) (sh R) (sh x) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using hf.shift
  have hG : Δ ⊢[PRAAx] rowBounds g (sh N) (sh S) (sh y) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using hg.shift
  have dF : Δ ⊢[PRAAx] rowRegular f (sh N) (sh L) (sh x) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using df.shift
  have dG : Δ ⊢[PRAAx] rowRegular g (sh N) (sh M) (sh y) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using dg.shift
  simpa [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,Δ,sh,X,Y] using
    diagonal_product_error f g (var 0) (sh N) (sh R) (sh S) (sh L) (sh M) (sh x) (sh y) hF hG dF dG

theorem actual_named_finite_products_multiply_closed (f g : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((rowBounds f (var 0) (var 1) (var 5) ⋏ rowBounds g (var 0) (var 2) (var 6)) ⟶
      (rowRegular f (var 0) (var 3) (var 5) ⋏ rowRegular g (var 0) (var 4) (var 6)) ⟶
      crossEquivalent (nameF (rowProduct f g)) (multiplyF (nameF f) (nameF g))
        (data (var 0) (var 1*var 2) (var 3*var 2+var 1*var 4) (pairT (var 5) (var 6)))
        (multiplyData (nameF f) (nameF g) (data (var 0) (var 1) (var 3) (var 5)) (data (var 0) (var 2) (var 4) (var 6)))) :=
  closeUniv 7 (.impI (.impI (named_product f g _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂
    Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianNamedFiniteProductAlgebra
