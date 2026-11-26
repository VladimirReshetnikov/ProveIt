import IPRADerivations.Analysis.RationalArithmetic.Powers.RationalReciprocalPowerTail
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalSumLinearity
import IPRADerivations.Analysis.Optimization.Convexity.RationalConvexClockRescale
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianCompactScalarMajorant

/-!
# Uniform reciprocal-square quadrature on positive affine panels

For the original left grid of step `1/(E*N)`, the sum of the weighted
reciprocal-square samples over `[a/E,(a+W)/E]` is at most `2*E/a`.
The same finite calculation allows a natural scalar multiplier. The
potential `2*S/k` decreases by at least the weighted row `S/k²`.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerReciprocalTail

open_ipra
open GaussianEuclideanDistanceName (fraction fraction_order fraction_represents)
open GaussianRationalHorner (positive_product scalar_congr)
open GaussianRationalSyntheticBounds (add_monotone)
open RationalArithmetic (add multiply)
open RationalArgmin (rationalLE rationalEq rationalLE_congr)
open RationalNonnegativePowers (fraction_congr fraction_multiply)
open RationalConvexClockRescale (fraction_rescale)
open RationalReciprocalPowerTail (zero_fraction add_zero_right)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def row (S k : PTm n) : PTm n := fraction S (k*k)
def potential (S k : PTm n) : PTm n := fraction (two*S) k
def body : PTm 2 := row (fstT (var 1)) (sndT (var 1)+var 0)
def prefixSum (S k r : PTm n) : PTm n := RationalFiniteSum.sum body r (pairT S k)
def conserved (S k r : PTm n) : Fm PTm n :=
  rationalLE (fraction zero one) (prefixSum S k r) ⋏
    rationalLE (add (prefixSum S k r) (potential S (k+r))) (potential S k)

def gridData (M a E N : PTm n) : PTm n := pairT (M*(E*N)*(E*N)) (a*N)
def quadrature (M a W E N : PTm n) : PTm n := prefixSum (M*(E*N)) (a*N) (W*N)

ipra_subst row
ipra_subst potential [two, one]
@[simp] theorem subst_prefix {m : ℕ} (σ : Fin n → PTm m) (S k r : PTm n) :
    Syn.subst σ (prefixSum S k r) = prefixSum (Syn.subst σ S) (Syn.subst σ k) (Syn.subst σ r) := by simp [prefixSum]
ipra_subst conserved

private theorem potential_congr (S : PTm n) {k l : PTm n} (e : Γ ⊢[PRAAx] k ≐ l) :
    Γ ⊢[PRAAx] potential S k ≐ potential S l := fraction_congr (.eqRefl _) e

private theorem term_at (S k i : PTm n) : Γ ⊢[PRAAx]
    RationalFiniteSum.term body i (pairT S k) ≐ row S (k+i) := by
  simp only [RationalFiniteSum.term,body,inst2,subst_row,subst_fstT,subst_sndT,
    PTm.subst_add,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have e := congrAdd (snd_pair (Γ := Γ) S k) (.eqRefl i)
  exact fraction_congr (fst_pair S k) (congrMul e e)

private theorem one_step (S k : PTm n) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    rationalLE (add (row S k) (potential S (succ k))) (potential S k) := by
  let d := k*k
  let l := succ k
  let A := S*l+(two*S)*d
  have hd : Γ ⊢[PRAAx] le one d := positive_product k k hk hk
  have hl := zero_lt_succ (Γ := Γ) k
  have hdl := positive_product d l hd hl
  have repr : Γ ⊢[PRAAx] RationalArithmetic.represents (add (row S k) (potential S l)) (ZT.ofNat A) (d*l) := by
    have h := RationalRepresentations.represents_add (Γ := Γ) (row S k) (potential S l) _ _ _ _
      (fraction_represents S d hd) (fraction_represents (two*S) l hl)
    apply scalar_congr (.eqRefl _) (hAB := .eqRefl _) (h := h)
    apply ZT.derive
    simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
    dsimp only [A]
    ipra_simps
  apply GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ hdl hk repr (fraction_represents _ _ hk)
  dsimp only [A,d,l]
  ipra_le 𝔞(S)*𝔞(k)*sl hk

private theorem conserve_zero (S k : PTm n) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] conserved S k zero := by
  have z := (RationalFiniteSum.sum_zero (Γ := Γ) body (pairT S k)).eqTrans zero_fraction.eqSymm
  have e := (RationalAlgebra.add_congr z (potential_congr S (add_zero k))).eqTrans
    ((RationalAlgebra.add_commutative _ _).eqTrans (add_zero_right _ (RationalNormalForm.normalize_well_formed _ _ hk)))
  exact .andI (rationalLE_congr (.eqRefl _) z.eqSymm (RationalArgmin.reflexive _))
    (rationalLE_congr e.eqSymm (.eqRefl _) (RationalArgmin.reflexive _))

private theorem conserve_succ (S k r : PTm n) (hk : Γ ⊢[PRAAx] le one k)
    (ih : Γ ⊢[PRAAx] conserved S k r) : Γ ⊢[PRAAx] conserved S k (succ r) := by
  have hkr := le_trans hk (le_add_right k r)
  have step := one_step S (k+r) hkr
  have next := (RationalFiniteSum.sum_succ (Γ := Γ) body r (pairT S k)).eqTrans
    (RationalAlgebra.add_congr (.eqRefl _) (term_at S k r))
  have e := (RationalAlgebra.add_congr
    next
    (potential_congr S (by ipra_ring : Γ ⊢[PRAAx] k+succ r ≐ succ (k+r)))).eqTrans
    (RationalAlgebra.add_associative _ _ _)
  have addStep := add_monotone (prefixSum S k r) (prefixSum S k r) _ _ (RationalArgmin.reflexive _) step
  have hn : Γ ⊢[PRAAx] rationalLE (fraction zero one) (row S (k+r)) :=
    fraction_order _ _ _ _ (le_refl one) (positive_product _ _ hkr hkr)
      (le_congr (mul_zero _).eqSymm (by ipra_ring : Γ ⊢[PRAAx] S ≐ S*one) (zero_le _))
  have base : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (fraction (zero : PTm n) one) :=
    RationalNormalForm.normalize_well_formed _ _ (le_refl one)
  have pos := rationalLE_congr (add_zero_right _ base) next.eqSymm (add_monotone _ _ _ _ ih.andE₁ hn)
  exact .andI pos (RationalArgmin.transitive (rationalLE_congr e.eqSymm (.eqRefl _) addStep) ih.andE₂)

private theorem conservation (S k r : PTm n) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] conserved S k r := by
  have hall : Γ ⊢[PRAAx] .all (conserved (Syn.shift S) (Syn.shift k) (var 0)) := by
    refine PRA.qfInd _ ⟨trivial,trivial⟩ ?_ ?_
    · simpa only [subst_conserved,Syn.subst_var,Syn.subst_inst_shift,Syn.inst_zero,ConciseIPRA.PTm.subst_zero] using
        conserve_zero S k hk
    · simp only [subst_conserved,subst_repl_shift]
      have hks : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift k) := by simpa [Fm.shift,Syn.shift] using hk.shift
      exact conserve_succ (Syn.shift S) (Syn.shift k) (var 0) hks.wk Prf.hyp0
  simpa only [subst_conserved,Syn.subst_var,Syn.subst_inst_shift,Syn.inst_zero] using hall.allE r

theorem prefix_bound (S k r : PTm n) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] rationalLE (prefixSum S k r) (potential S k) := by
  have hkr := le_trans hk (le_add_right k r)
  have hpos : Γ ⊢[PRAAx] rationalLE (fraction zero one) (potential S (k+r)) :=
    fraction_order _ _ _ _ (le_refl one) hkr
      (le_congr (mul_zero _).eqSymm
        (by ipra_ring : Γ ⊢[PRAAx] two*S ≐ (two*S)*one) (zero_le _))
  have monoton := add_monotone (prefixSum S k r) (prefixSum S k r) _ _ (RationalArgmin.reflexive _) hpos
  have first := rationalLE_congr
    (add_zero_right _ (RationalFiniteSum.sum_well_formed body r (pairT S k))) (.eqRefl _) monoton
  exact RationalArgmin.transitive first (conservation S k r hk).andE₂

theorem quadrature_bound (M a W E N : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] rationalLE (quadrature M a W E N) (fraction (two*M*E) a) := by
  have e : Γ ⊢[PRAAx] potential (M*(E*N)) (a*N) ≐ fraction (two*M*E) a :=
    (fraction_congr (by ipra_ring : Γ ⊢[PRAAx] two*(M*(E*N)) ≐ (two*M*E)*N) (.eqRefl _)).eqTrans
      (fraction_rescale (two*M*E) a N ha hN)
  exact rationalLE_congr (.eqRefl _) e (prefix_bound _ _ _ (positive_product a N ha hN))

theorem grid_term (i M a E N : PTm n) : Γ ⊢[PRAAx]
    RationalFiniteSum.term body i (gridData M a E N) ≐ row (M*(E*N)*(E*N)) (a*N+i) :=
  term_at (M*(E*N)*(E*N)) (a*N) i

theorem affine_grid_term (i M a W E N : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hW : Γ ⊢[PRAAx] le one W) (hN : Γ ⊢[PRAAx] le one N) :
    let t := GaussianCompactRiemannName.grid i (W*N) a W E
    Γ ⊢[PRAAx] RationalFiniteSum.term body i (gridData M a E N) ≐
      row (M*sndT t*sndT t) (fstT t) := by
  dsimp only
  let t := GaussianCompactRiemannName.grid i (W*N) a W E
  let k := a*N+i
  let D := E*N
  have eNum : Γ ⊢[PRAAx] fstT t ≐ W*k :=
    (fst_pair _ _).eqTrans (by dsimp only [k]; ipra_ring)
  have eDen : Γ ⊢[PRAAx] sndT t ≐ W*D :=
    (snd_pair _ _).eqTrans (by dsimp only [D]; ipra_ring)
  have e : Γ ⊢[PRAAx] row (M*sndT t*sndT t) (fstT t) ≐ fraction ((M*D*D)*(W*W)) ((k*k)*(W*W)) :=
    fraction_congr ((congrMul (congrMul (.eqRefl _) eDen) eDen).eqTrans (by ipra_ring))
      ((congrMul eNum eNum).eqTrans (by ipra_ring))
  have hk := le_trans (positive_product a N ha hN) (le_add_right (a*N) i)
  exact (grid_term i M a E N).eqTrans
    ((fraction_rescale (M*D*D) (k*k) (W*W) (positive_product k k hk hk) (positive_product W W hW hW)).eqSymm.eqTrans e.eqSymm)

private theorem weighted_term (i M a E N : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    RationalFiniteSum.term (RationalSumLinearity.scaledBody body) i
        (pairT (fraction one (E*N)) (gridData M a E N)) ≐
      RationalFiniteSum.term body i (pairT (M*(E*N)) (a*N)) := by
  let D := E*N
  let k := a*N+i
  have hD := positive_product E N hE hN
  have hk := le_trans (positive_product a N ha hN) (le_add_right (a*N) i)
  have hk2 := positive_product k k hk hk
  exact (RationalSumLinearity.scaled_term body i (fraction one D) (gridData M a E N)).eqTrans
    ((RationalAlgebra.multiply_congr (.eqRefl _) (grid_term i M a E N)).eqTrans
      ((fraction_multiply one D (M*D*D) (k*k) hD hk2).eqTrans
        ((fraction_congr (one_mul _) (mul_comm _ _)).eqTrans
          ((fraction_rescale (M*D) (k*k) D hk2 hD).eqTrans (term_at (M*D) (a*N) i).eqSymm))))

theorem original_scalar_left (M a W E N : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hW : Γ ⊢[PRAAx] le one W) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianCompactScalarMajorant.scalarLeft body (W*N) (gridData M a E N) W E ≐ quadrature M a W E N := by
  let h := fraction one (E*N)
  let s (v : PTm n) := Syn.shift v
  have hs : Γ ⊢[PRAAx] fraction W (E*(W*N)) ≐ h :=
    (fraction_congr (one_mul W).eqSymm (by ipra_ring : Γ ⊢[PRAAx] E*(W*N) ≐ (E*N)*W)).eqTrans
      (fraction_rescale one (E*N) W (positive_product E N hE hN) hW)
  have sa : Γ.map Fm.shift ⊢[PRAAx] le one (s a) := by simpa [Fm.shift,Syn.shift,one,s] using ha.shift
  have se : Γ.map Fm.shift ⊢[PRAAx] le one (s E) := by simpa [Fm.shift,Syn.shift,one,s] using hE.shift
  have sn : Γ.map Fm.shift ⊢[PRAAx] le one (s N) := by simpa [Fm.shift,Syn.shift,one,s] using hN.shift
  have terms : Γ ⊢[PRAAx] RationalFiniteSum.termwiseEq (RationalSumLinearity.scaledBody body) body (W*N)
      (pairT h (gridData M a E N)) (pairT (M*(E*N)) (a*N)) := by
    refine .allI (.impI ?_)
    simp only [GaussianEuclideanDistanceName.subst_fraction,subst_pairT,PTm.subst_mul,gridData,Syn.shift,h,
      one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
    have e := weighted_term (Γ := lt (var 0) (s W*s N) :: Γ.map Fm.shift)
      (var 0) (s M) (s a) (s E) (s N) sa.wk se.wk sn.wk
    exact RationalArgmin.rationalEq_congr e.eqSymm (.eqRefl _)
      (RationalArgmin.antisymm (RationalArgmin.reflexive _) (RationalArgmin.reflexive _))
  exact (RationalAlgebra.multiply_congr hs (.eqRefl _)).eqTrans
    ((RationalSumLinearity.sum_homogeneous body (W*N) h (gridData M a E N)).eqSymm.eqTrans
      (RationalFiniteSum.sum_ext (RationalSumLinearity.scaledBody body) body (W*N) _ _ terms))

theorem original_scalar_left_bound (M a W E N : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hW : Γ ⊢[PRAAx] le one W) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    rationalLE (GaussianCompactScalarMajorant.scalarLeft body (W*N) (gridData M a E N) W E) (fraction (two*M*E) a) :=
  rationalLE_congr (original_scalar_left M a W E N ha hW hE hN).eqSymm (.eqRefl _) (quadrature_bound M a W E N ha hN)

theorem original_scalar_left_embedded_bound (M a W E N : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hW : Γ ⊢[PRAAx] le one W) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (RationalGaussianEmbedding.embed
      (GaussianCompactScalarMajorant.scalarLeft body (W*N) (gridData M a E N) W E)) (two*M*E) a := by
  let v := GaussianCompactScalarMajorant.scalarLeft body (W*N) (gridData M a E N) W E
  let b := RationalSupMetric.denominatorOf v
  let u := GaussianPositiveRealArithmetic.numerator v
  let bound := two*M*E
  have hbase := GaussianRationalL1.nonnegative_of_representation _ zero one (le_refl one)
    (fraction_represents (Γ := Γ) zero one (le_refl one))
  have rawPos := GaussianRationalL1.nonnegative_of_lower _ (quadrature M a W E N) hbase
    (conservation (M*(E*N)) (a*N) (W*N) (positive_product _ _ ha hN)).andE₁
  have hs : Γ ⊢[PRAAx] GaussianPositiveRealArithmetic.sign v :=
    GaussianPositiveRealArithmetic.sign_congr (original_scalar_left M a W E N ha hW hE hN).eqSymm rawPos
  have hb : Γ ⊢[PRAAx] le one b := RationalArgmin.denominator_positive v
  have rep := GaussianPositiveRealArithmetic.natural_representation v hs
  have hle := GaussianRationalMetric.comparison_to_cleared v (fraction bound a) u bound b a rep
    (fraction_represents bound a ha) (original_scalar_left_bound M a W E N ha hW hE hN)
  apply GaussianRationalMetric.bounded_of_cleared _ (GaussianDominantPairAlgebra.radiusNumerator u) b bound a hb ha
    (RationalGaussianEmbedding.embed_from_representation _ _ _ rep)
  exact le_congr ((congrMul (.eqRefl _) (GaussianDominantPairAlgebra.radius_numerator_norm u)).eqTrans (by ipra_ring)).eqSymm
    (by ipra_ring) (AnalyticNumberTheory.PhiLower.le_mul_mono hle hle)

theorem actual_affine_reciprocal_square_quadrature_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (var 1) ⟶ le one (var 4) ⟶ rationalLE (quadrature (var 0) (var 1) (var 2) (var 3) (var 4))
        (fraction (two*var 0*var 3) (var 1))) :=
  closeUniv 5 (.impI (.impI (quadrature_bound _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_affine_reciprocal_square_original_grid_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((le one (var 1) ⋏ (le one (var 2) ⋏ (le one (var 3) ⋏ le one (var 4)))) ⟶
        GaussianRationalMetric.bounded (RationalGaussianEmbedding.embed
          (GaussianCompactScalarMajorant.scalarLeft body (var 2*var 4) (gridData (var 0) (var 1) (var 3) (var 4))
            (var 2) (var 3))) (two*var 0*var 3) (var 1)) :=
  closeUniv 5 (.impI (original_scalar_left_embedded_bound _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerReciprocalTail
