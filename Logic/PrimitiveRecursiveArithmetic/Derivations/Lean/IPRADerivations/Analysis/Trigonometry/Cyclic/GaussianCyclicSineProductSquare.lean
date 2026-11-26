import IPRADerivations.Analysis.Trigonometry.Cyclic.GaussianCyclicChordSquare
import IPRADerivations.Analysis.Trigonometry.Cyclic.GaussianCyclicRootProduct
import IPRADerivations.Analysis.Names.FiniteOperations.Products.GaussianNamedFiniteProductMap

/-!
# Squared sine product from the literal cyclic root reconstruction

Both products use the finite precision-first row loop over all nontrivial
roots. Its cyclic-chord instance agrees exactly with the reconstructed
product at one. The pointwise chord-square estimate then gives the
uniform convergence of the square of the doubled real sine product.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianCyclicSineProductSquare

open_ipra
open GaussianCyclicChordSquare (chord chordRadius doubledSine doubled_sine_bound chord_bound squareError
  twiceSineRadius sineSquareRadius compareRadius chordError unitError square_error)
open GaussianCyclicExponentialSeparation (fine clock clock_fine)
open GaussianCyclicRootProduct (roots roots_at reconstruction_at)
open GaussianNamedFiniteProduct (sample sample_zero sample_succ sample_distance rowBoundsAt rowDistance amplification)
open GaussianNamedFiniteProductMap (normF squareF norm_at square_at sample_norm sample_square)
open GaussianRationalNormSquareTransport (value value_congr)
open GaussianRationalConjugation (point point_bound)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalHorner (qmul ofGaussian)
open GaussianRationalReciprocal (qone qone_bounded bounded_product bound_congr)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalSyntheticDivision (qsub_congr qmul_congr)
open GaussianRationalReconstruction (factors factors_zero factors_succ product)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (bounded_radius_mono unit unit_positive)
open GaussianNamedNaturalScale (natural_point_bound)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (N x : PTm n) : PTm n := pairT N x
def index (N i : PTm n) : PTm n := monus N (succ i)
def chordBody : PTm 3 :=
  chord (var 0) (succ (index (fstT (var 2)) (var 1))) (succ (fstT (var 2))) (sndT (var 2))
def sineBody : PTm 3 :=
  doubledSine (var 0) (succ (index (fstT (var 2)) (var 1))) (succ (fstT (var 2))) (sndT (var 2))
def chordF : PR 3 := PTm.toPR chordBody
def sineF : PR 3 := PTm.toPR sineBody
def radius : PTm n := chordRadius*chordRadius+sineSquareRadius
def normBudget (N : PTm n) : PTm n :=
  (succ N+GaussianNamedFiniteProduct.radius chordRadius N)*GaussianCyclicRootProduct.budget N+
    amplification radius N*squareError

ipra_subst data

ipra_subst index

private theorem readback (g : PTm 4) (p N x i : PTm n) :
    Γ ⊢[PRAAx] Syn.subst ![p,fstT (data N x),sndT (data N x),i] g ≐ Syn.subst ![p,N,x,i] g :=
  Prf.eqCongr g (σ := ![p,fstT (data N x),sndT (data N x),i]) (σ' := ![p,N,x,i])
    (fun j => by fin_cases j; exact .eqRefl _; exact fst_pair _ _; exact snd_pair _ _; exact .eqRefl _)

theorem chord_at (p N x i : PTm n) :
    Γ ⊢[PRAAx] ap3 chordF p i (data N x) ≐ chord p (succ (index N i)) (succ N) x := by
  have e := readback (Γ := Γ) (chord (var 0) (succ (index (var 1) (var 3))) (succ (var 1)) (var 2)) p N x i
  have pr : Γ ⊢[PRAAx] ap3 chordF p i (data N x) ≐
      chord p (succ (index (fstT (data N x)) i)) (succ (fstT (data N x))) (sndT (data N x)) := by
    simpa [chordF,chordBody,ap3] using toPR_eq (Γ := Γ) chordBody ![p,i,data N x]
  exact pr.eqTrans (by simpa using e)

theorem sine_at (p N x i : PTm n) :
    Γ ⊢[PRAAx] ap3 sineF p i (data N x) ≐ doubledSine p (succ (index N i)) (succ N) x := by
  have e := readback (Γ := Γ) (doubledSine (var 0) (succ (index (var 1) (var 3))) (succ (var 1)) (var 2)) p N x i
  have pr : Γ ⊢[PRAAx] ap3 sineF p i (data N x) ≐
      doubledSine p (succ (index (fstT (data N x)) i)) (succ (fstT (data N x))) (sndT (data N x)) := by
    simpa [sineF,sineBody,ap3] using toPR_eq (Γ := Γ) sineBody ![p,i,data N x]
  exact pr.eqTrans (by simpa using e)

private theorem index_lt (N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] lt (index N i) N := by
  have E : Γ ⊢[PRAAx] N ≐ succ i+index N i := eq_add_of_le hi
  exact le_of_eq_add (d := i) (E.eqTrans (by ipra_ring))

private theorem index_source (N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] GaussianCyclicExponentialRoots.source (succ (index N i)) (succ N) :=
  .andI (zero_lt_succ N) (le_trans (index_lt N i hi) (le_succ_self N))

private def factorLaw (p N x i : PTm n) : Fm PTm n := le i N ⟶
  factors (roots p N x) N qone i ≐ sample chordF p i (data N x)

@[simp] private theorem subst_factorLaw {L : ℕ} (σ : Fin n → PTm L) (p N x i : PTm n) :
    (factorLaw p N x i).subst σ = factorLaw (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ i) := by
  simp [factorLaw]

private theorem factor_step (p N x i : PTm n) (ih : Γ ⊢[PRAAx] factorLaw p N x i) :
    Γ ⊢[PRAAx] factorLaw p N x (succ i) := by
  let Δ := le (succ i) N :: Γ
  have hi : Δ ⊢[PRAAx] lt i N := Prf.hyp0
  have ih' : Δ ⊢[PRAAx] factors (roots p N x) N qone i ≐ sample chordF p i (data N x) :=
    .impE ih.wk (le_of_lt hi)
  have eq := (qsub_congr (.eqRefl qone) (roots_at p N x (index N i) (index_lt N i hi))).eqTrans
    (chord_at p N x i).eqSymm
  exact .impI ((factors_succ _ _ _ _).eqTrans ((qmul_congr eq ih').eqTrans
    ((qmul_commutative _ _).eqTrans (sample_succ _ _ _ _).eqSymm)))

theorem product_agrees (p N x : PTm n) :
    Γ ⊢[PRAAx] product (roots p N x) N qone ≐ sample chordF p N (data N x) := by
  have h : Γ ⊢[PRAAx] .all (factorLaw (Syn.shift p) (Syn.shift N) (Syn.shift x) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_factorLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI ((factors_zero _ _ _).eqTrans (sample_zero _ _ _).eqSymm).wk
    · simpa only [subst_factorLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        factor_step (Γ := factorLaw (Syn.shift p) (Syn.shift N) (Syn.shift x) (var 0) :: Γ.map Fm.shift)
          (Syn.shift p) (Syn.shift N) (Syn.shift x) (var 0) Prf.hyp0
  have e : Γ ⊢[PRAAx] factorLaw p N x N := by
    simpa only [subst_factorLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE N
  exact .impE e (le_refl N)

theorem chord_rows (p N x : PTm n) : Γ ⊢[PRAAx] rowBoundsAt chordF p N chordRadius (data N x) := by
  refine .allI (.impI ?_)
  have h := chord_bound (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) (Syn.shift p) (succ (index (Syn.shift N) (var 0))) (succ (Syn.shift N)) (Syn.shift x)
    (index_source (Syn.shift N) (var 0) Prf.hyp0)
  simpa [rowBoundsAt,Syn.shift,chordRadius,one] using
    bound_congr (chord_at (Syn.shift p) (Syn.shift N) (Syn.shift x) (var 0)).eqSymm (.eqRefl _) (.eqRefl _) h

theorem norm_rows (p N x : PTm n) : Γ ⊢[PRAAx] rowBoundsAt (normF chordF) p N radius (data N x) := by
  refine .allI (.impI ?_)
  let t := Syn.shift p
  let j := Syn.shift N
  let y := Syn.shift x
  let i : PTm (n+1) := var 0
  let Δ := lt i j :: Γ.map Fm.shift
  let q := ap3 chordF t i (data j y)
  have h : Δ ⊢[PRAAx] bounded (chord t (succ (index j i)) (succ j) y) chordRadius one :=
    chord_bound _ _ _ _ (index_source j i Prf.hyp0)
  have b := bound_congr (chord_at t j y i).eqSymm (.eqRefl _) (.eqRefl _) h
  have c : Δ ⊢[PRAAx] bounded (value q) (chordRadius*chordRadius) one :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
      (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) b (point_bound _ _ _ (le_refl one) b))
  have d : Δ ⊢[PRAAx] bounded (value q) radius one := bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
    (le_congr (by ipra_ring) (by unfold radius; ipra_ring) (le_add_right (chordRadius*chordRadius) sineSquareRadius)) c
  simpa [rowBoundsAt,Syn.shift,t,j,y,i,Δ,radius,chordRadius,sineSquareRadius,twiceSineRadius,one] using
    bound_congr (norm_at chordF t i (data j y)).eqSymm (.eqRefl _) (.eqRefl _) d

theorem square_rows (p N x : PTm n) : Γ ⊢[PRAAx] rowBoundsAt (squareF sineF) p N radius (data N x) := by
  refine .allI (.impI ?_)
  let t := Syn.shift p
  let j := Syn.shift N
  let y := Syn.shift x
  let i : PTm (n+1) := var 0
  let Δ := lt i j :: Γ.map Fm.shift
  let q := ap3 sineF t i (data j y)
  have h : Δ ⊢[PRAAx] bounded (doubledSine t (succ (index j i)) (succ j) y) twiceSineRadius one :=
    doubled_sine_bound _ _ _ _ (index_source j i Prf.hyp0)
  have b := bound_congr (sine_at t j y i).eqSymm (.eqRefl _) (.eqRefl _) h
  have c : Δ ⊢[PRAAx] bounded (qmul q q) sineSquareRadius one :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
      (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) b b)
  have d : Δ ⊢[PRAAx] bounded (qmul q q) radius one := bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
    (le_congr (by ipra_ring) (by unfold radius; ipra_ring) (le_add_left sineSquareRadius (chordRadius*chordRadius))) c
  simpa [rowBoundsAt,Syn.shift,t,j,y,i,Δ,radius,chordRadius,sineSquareRadius,twiceSineRadius,one] using
    bound_congr (square_at sineF t i (data j y)).eqSymm (.eqRefl _) (.eqRefl _) d

theorem row_square_error (p N x : PTm n) :
    Γ ⊢[PRAAx] rowDistance (normF chordF) (squareF sineF) p p N squareError (unit p) (data N x) (data N x) := by
  refine .allI (.impI ?_)
  let t := Syn.shift p
  let j := Syn.shift N
  let y := Syn.shift x
  let i : PTm (n+1) := var 0
  let Δ := lt i j :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] GaussianCyclicExponentialRoots.source (succ (index j i)) (succ j) := index_source j i Prf.hyp0
  have a := (norm_at (Γ := Δ) chordF t i (data j y)).eqTrans (value_congr (chord_at t j y i))
  have b := (square_at (Γ := Δ) sineF t i (data j y)).eqTrans (qmul_congr (sine_at t j y i) (sine_at t j y i))
  simpa [rowDistance,Syn.shift,t,j,y,i,Δ,squareError,chordRadius,compareRadius,chordError,unitError,
    sineSquareRadius,twiceSineRadius] using
    distance_congr a.eqSymm b.eqSymm (.eqRefl _) (.eqRefl _) (square_error _ _ _ _ hs)

private theorem naturalPoint_real (m : PTm n) : Γ ⊢[PRAAx] point (naturalPoint m) ≐ naturalPoint m := by
  have r := natural_point_represents (Γ := Γ) m
  have p := GaussianRationalConjugation.point_represents _ _ _ (le_refl one) r
  apply GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianRationalConjugation.point_canonical _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl one)) (le_refl one) _ r
  apply GaussianRationalHorner.represents_congr (.eqRefl _) _ (.eqRefl _) p
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRationalReciprocal.re_conjugate,GaussianRationalReciprocal.im_conjugate,
      GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.im_one] <;> ring

theorem product_square_error (p N x : PTm n) (hf : Γ ⊢[PRAAx] fine (succ N) p) :
    Γ ⊢[PRAAx] distanceBounded
      (qmul (naturalPoint (succ N)) (naturalPoint (succ N)))
      (qmul (sample sineF p N (data N x)) (sample sineF p N (data N x))) (normBudget N) (unit p) := by
  let m := succ N
  let M := naturalPoint m
  let C := sample chordF p N (data N x)
  let hp := unit_positive (Γ := Γ) p
  have near := distance_congr (.eqRefl _) (product_agrees p N x) (.eqRefl _) (.eqRefl _) (reconstruction_at p N x hf)
  have hC := GaussianNamedFiniteProduct.sample_bound (Γ := Γ) chordF p N chordRadius (data N x) (chord_rows p N x)
  have first := distance_congr (qmul_congr (.eqRefl M) (naturalPoint_real m)) (sample_norm chordF p N (data N x))
    (.eqRefl _) (.eqRefl _) (GaussianRationalNormSquareTransport.distance _ _ _ _ _ _ hp (natural_point_bound m) hC near)
  have last := distance_congr (.eqRefl _) (sample_square sineF p N (data N x)).eqSymm (.eqRefl _) (.eqRefl _)
    (sample_distance (normF chordF) (squareF sineF) p p N radius squareError (unit p) (data N x) (data N x) hp
      (norm_rows p N x) (square_rows p N x) (row_square_error p N x))
  exact distance_triangle_same _ _ _ _ _ _ hp first last

theorem actual_original_cyclic_sine_product_square_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (distanceBounded (qmul (naturalPoint (succ (var 1))) (naturalPoint (succ (var 1))))
        (qmul (sample sineF (clock (succ (var 1)) (var 2)) (var 1) (data (var 1) (var 0)))
          (sample sineF (clock (succ (var 1)) (var 2)) (var 1) (data (var 1) (var 0))))
        (normBudget (var 1)) (unit (clock (succ (var 1)) (var 2)))) :=
  closeUniv 3 (product_square_error _ _ _ (clock_fine _ _))

end LeanProofs.IPRA.Analysis.GaussianCyclicSineProductSquare
