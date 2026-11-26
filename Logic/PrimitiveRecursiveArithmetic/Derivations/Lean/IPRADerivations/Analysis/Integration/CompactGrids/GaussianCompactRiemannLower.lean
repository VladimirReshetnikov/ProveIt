import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalRepresentedUpper
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactRiemannName
import IPRADerivations.Analysis.RationalArithmetic.RationalGaussianRealPart
import IPRADerivations.Analysis.RationalArithmetic.GaussianPositiveRealArithmetic

/-!
# Lower estimate of the real part of an actual affine-grid quadrature

A uniform lower estimate at the actual rows gives the same lower
estimate times the interval length. The one-sided tolerance is scaled
by the same length. The induction uses the independently denominated,
signed real coordinates of the rows.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCompactRiemannLower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalValueBounds (upper)
open RationalSupMetric (numeratorOf denominatorOf)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianCompactRiemannName (sampleBody sampleData quadrature grid sample_body_at)
open GaussianRationalRiemannRefinement (leftSum weight)
open GaussianRationalHorner (qmul positive_product)
open RationalGaussianRealPart (realBody real_sum real_product)
open PolynomialBisection (slack)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def rows (t : PTm 2) (N x A B U V : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift N) ⟶ upper (fraction (Syn.shift A) (Syn.shift B))
    (RationalFiniteSum.term t (var 0) (Syn.shift x)) (Syn.shift U) (Syn.shift V))

@[simp] theorem subst_rows {l : ℕ} (σ : Fin n → PTm l) (t : PTm 2) (N x A B U V : PTm n) :
    (rows t N x A B U V).subst σ = rows t (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ A)
      (Syn.subst σ B) (Syn.subst σ U) (Syn.subst σ V) := by
  simp [rows,GaussianEuclideanDistanceName.fraction,Syn.subst_shift,Syn.shift_subst]

private theorem row_at (t : PTm 2) (N x A B U V i : PTm n)
    (h : Γ ⊢[PRAAx] rows t N x A B U V) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] upper (fraction A B) (RationalFiniteSum.term t i x) U V := by
  apply Prf.impE ?_ hi
  simpa [rows,GaussianEuclideanDistanceName.fraction,Syn.subst_inst_shift] using h.allE i

def floorNumerator (A B U V : PTm n) : ZT n := ZT.ofNat (A*V)-ZT.ofNat (U*B)
def prefixLeft (t : PTm 2) (i x A B U V : PTm n) : ZT n :=
  floorNumerator A B U V * ZT.ofNat (i*RationalFiniteSum.denominator t i x)
def prefixRight (t : PTm 2) (i x B V : PTm n) : ZT n :=
  RationalFiniteSum.numerator t i x * ZT.ofNat (B*V)
def prefixLaw (t : PTm 2) (N i x A B U V : PTm n) : Fm PTm n :=
  le i N ⟶ zle (prefixLeft t i x A B U V) (prefixRight t i x B V)

@[simp] theorem subst_floorNumerator {l : ℕ} (σ : Fin n → PTm l) (A B U V : PTm n) :
    (floorNumerator A B U V).subst σ =
      floorNumerator (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ U) (Syn.subst σ V) := by
  simp [floorNumerator]
@[simp] theorem subst_prefixLaw {l : ℕ} (σ : Fin n → PTm l) (t : PTm 2) (N i x A B U V : PTm n) :
    (prefixLaw t N i x A B U V).subst σ = prefixLaw t (Syn.subst σ N) (Syn.subst σ i)
      (Syn.subst σ x) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ U) (Syn.subst σ V) := by
  have hz (v w : ZT n) : (zle v w).subst σ = zle (v.subst σ) (w.subst σ) := by
    simp [zle,ZT.subst]
  unfold prefixLaw
  rw [Fm.subst_imp,hz,subst_le]
  simp [prefixLeft,prefixRight]

private theorem signed_row (t : PTm 2) (i x A B U V : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] upper (fraction A B) (RationalFiniteSum.term t i x) U V) : Γ ⊢[PRAAx]
    zle (floorNumerator A B U V * ZT.ofNat (denominatorOf (RationalFiniteSum.term t i x)))
      (numeratorOf (RationalFiniteSum.term t i x) * ZT.ofNat (B*V)) := by
  let c := RationalFiniteSum.term t i x
  have order := RationalRepresentedUpper.to_signed _ c (ZT.ofNat A) (numeratorOf c) B (denominatorOf c)
    U V (fraction_represents A B hB) (RationalRepresentations.represents_self c) h
  have value := zle_toZ order
  apply zle_of_toZ (slack (RationalRepresentedUpper.left (ZT.ofNat A) (denominatorOf c) V)
    (RationalRepresentedUpper.right (numeratorOf c) B (denominatorOf c) U V))
  simp only [RationalRepresentedUpper.left,RationalRepresentedUpper.right,floorNumerator,slack,
    ZT.toZ_mul,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_ofNat,Q.mk_mul,map_mul] at value ⊢
  linear_combination value

private theorem prefix_zero (t : PTm 2) (x A B U V : PTm n) : Γ ⊢[PRAAx]
    zle (prefixLeft t zero x A B U V) (prefixRight t zero x B V) := by
  apply zle_of_toZ zero
  have ep := natEq (RationalFiniteSum.positive_zero (Γ := Γ) t x)
  have en := natEq (RationalFiniteSum.negative_zero (Γ := Γ) t x)
  simp only [prefixLeft,prefixRight,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul,Q.mk_zero,map_zero]
  simp only [RationalFiniteSum.numerator,ZT.toZ,ep,en,sub_self]
  ring

private theorem prefix_step (t : PTm 2) (i x A B U V : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] upper (fraction A B) (RationalFiniteSum.term t i x) U V)
    (ih : Γ ⊢[PRAAx] zle (prefixLeft t i x A B U V) (prefixRight t i x B V)) : Γ ⊢[PRAAx]
    zle (prefixLeft t (succ i) x A B U V) (prefixRight t (succ i) x B V) := by
  let c := RationalFiniteSum.term t i x
  let D := RationalFiniteSum.denominator t i x
  let F := denominatorOf c
  have row := zle_toZ (signed_row t i x A B U V hB h)
  have pref := zle_toZ ih
  apply zle_of_toZ (F*slack (prefixLeft t i x A B U V) (prefixRight t i x B V) +
    D*slack (floorNumerator A B U V * ZT.ofNat F) (numeratorOf c*ZT.ofNat (B*V)))
  have ed := natEq (RationalFiniteSum.denominator_succ (Γ := Γ) t i x)
  have en := ZT.toZ_eq (RationalFiniteSum.numerator_succ (Γ := Γ) t i x)
  simp only [prefixLeft,prefixRight,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul]
  rw [ed,en]
  dsimp only [F,D,c,slack] at *
  simp only [prefixLeft,prefixRight,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat,Q.mk_mul,map_mul,
    Q.mk_add,map_add,Q.mk_succ,map_one] at row pref ⊢
  linear_combination 𝔞(denominatorOf (RationalFiniteSum.term t i x))*pref+
    𝔞(RationalFiniteSum.denominator t i x)*row

theorem signed_prefix (t : PTm 2) (N x A B U V : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] rows t N x A B U V) : Γ ⊢[PRAAx]
    zle (prefixLeft t N x A B U V) (prefixRight t N x B V) := by
  have all : Γ ⊢[PRAAx] .all (prefixLaw t (Syn.shift N) (var 0) (Syn.shift x)
      (Syn.shift A) (Syn.shift B) (Syn.shift U) (Syn.shift V)) := by
    refine PRA.qfInd _ (by simp [prefixLaw,zle,Fm.QF,le_QF]) ?_ ?_
    · have result : Γ ⊢[PRAAx] prefixLaw t N zero x A B U V := by
        unfold prefixLaw
        exact Prf.impI (prefix_zero t x A B U V).wk
      simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using result
    · let Δ := Γ.map Fm.shift
      let body := prefixLaw t (Syn.shift N) (var 0) (Syn.shift x)
        (Syn.shift A) (Syn.shift B) (Syn.shift U) (Syn.shift V)
      let bound := le (succ (var 0 : PTm (n+1))) (Syn.shift N)
      have premise : bound :: body :: Δ ⊢[PRAAx] le (var 0) (Syn.shift N) :=
        le_trans (le_succ_self _) Prf.hyp0
      have ih : bound :: body :: Δ ⊢[PRAAx]
          zle (prefixLeft t (var 0) (Syn.shift x) (Syn.shift A) (Syn.shift B) (Syn.shift U) (Syn.shift V))
              (prefixRight t (var 0) (Syn.shift x) (Syn.shift B) (Syn.shift V)) :=
        Prf.impE (Prf.hyp1 : bound :: body :: Δ ⊢[PRAAx] body) premise
      have denom : Δ ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift,Δ] using hB.shift
      have source : Δ ⊢[PRAAx] rows t (Syn.shift N) (Syn.shift x) (Syn.shift A) (Syn.shift B)
          (Syn.shift U) (Syn.shift V) := by simpa [Fm.shift,Syn.shift,Δ] using h.shift
      have row := row_at t _ _ _ _ _ _ (var 0) source.wk.wk
        (Prf.hyp0 : bound :: body :: Δ ⊢[PRAAx] bound)
      have result : body :: Δ ⊢[PRAAx] prefixLaw t (Syn.shift N) (succ (var 0)) (Syn.shift x)
          (Syn.shift A) (Syn.shift B) (Syn.shift U) (Syn.shift V) := by
        unfold prefixLaw
        exact Prf.impI (prefix_step t (var 0) (Syn.shift x) (Syn.shift A) (Syn.shift B)
          (Syn.shift U) (Syn.shift V) denom.wk.wk row ih)
      simpa only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using result
  have out : Γ ⊢[PRAAx] prefixLaw t N N x A B U V := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  exact Prf.impE out (le_refl N)

private theorem weighted_representation (f : PTm 2) (N x C E : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (fstT (leftSum f N x C E))
      (ZT.ofNat C*RationalFiniteSum.numerator (realBody f) N x)
      (E*N*RationalFiniteSum.denominator (realBody f) N x) := by
  let w := weight C E N
  let s := GaussianRationalFiniteSum.sum f N x
  let t := realBody f
  have den := positive_product E N hE hN
  have hc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical w :=
    GaussianRationalHorner.ofGaussian_canonical _ _ den
  have wrep : Γ ⊢[PRAAx] GaussianRationalHorner.represents w
      (RationalGaussianEmbedding.native (ZT.ofNat C)) (E*N) := by
    apply GaussianRationalHorner.represents_congr (.eqRefl _) _ (.eqRefl _)
      (GaussianRationalHorner.ofGaussian_represents _ _ den)
    apply GaussianRootAlgebra.equal_of_values
    all_goals
      simp [RationalGaussianEmbedding.native,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
        GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,ComplexLogarithmRemainder.eval_re_code,
        ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]
  have wp := GaussianPositiveRealArithmetic.positive_from_representation w C (E*N) hc den wrep
  have axis := RationalGaussianEmbedding.canonical_axis_roundtrip w hc wp.andE₁
  have order := (congrFst ((GaussianRationalPowerAlgebra.qmul_commutative w s).eqTrans
    (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl s) axis.eqSymm))).eqTrans (real_product s (fstT w))
  have swapped := order.eqTrans ((RationalAlgebra.multiply_commutative _ _).eqTrans
    (RationalAlgebra.multiply_congr (.eqRefl (fstT w)) (real_sum f N x)))
  have scalarWeight : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT w) (ZT.ofNat C) (E*N) :=
    GaussianRationalHorner.scalar_congr (.eqRefl _) (by
      apply ZT.derive
      simp [RationalGaussianEmbedding.native,ComplexLogarithmRemainder.eval_re_code]) (.eqRefl _) wrep.andE₁
  have rep := RationalRepresentations.represents_multiply (fstT w) (RationalFiniteSum.sum t N x)
    (ZT.ofNat C) _ (E*N) _ scalarWeight (RationalFiniteSum.sum_value t N x)
  exact GaussianRationalHorner.scalar_congr swapped.eqSymm (ZT.derive rfl) (.eqRefl _) rep

/-- Literal affine quadrature, including zero width, with its exact
length factor in both the main term and the one-sided tolerance. -/
theorem left_sum_lower (f : PTm 2) (N x C E A B U V : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N)
    (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] rows (realBody f) N x A B U V) : Γ ⊢[PRAAx]
    upper (fraction (C*A) (E*B)) (fstT (leftSum f N x C E)) (C*U) (E*V) := by
  let t := realBody f
  let L := prefixLeft t N x A B U V
  let R := prefixRight t N x B V
  let D := RationalFiniteSum.denominator t N x
  have pref := zle_toZ (signed_prefix t N x A B U V hB h)
  have hEB := positive_product E B hE hB
  have hOut := positive_product _ _ (positive_product E N hE hN) (RationalFiniteSum.denominator_positive t N x)
  apply RationalRepresentedUpper.from_signed _ _ (ZT.ofNat (C*A))
    (ZT.ofNat C*RationalFiniteSum.numerator t N x) (E*B) (E*N*D) (C*U) (E*V)
    hEB hOut (fraction_represents _ _ hEB) (weighted_representation f N x C E hE hN)
  apply zle_of_toZ (C*E*E*slack L R)
  dsimp only [L,R,D]
  simp only [prefixLeft,prefixRight,floorNumerator,RationalRepresentedUpper.left,
    RationalRepresentedUpper.right,slack,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul]
    at pref ⊢
  linear_combination (𝔞(C)*𝔞(E)*𝔞(E))*pref

end LeanProofs.IPRA.Analysis.GaussianCompactRiemannLower
