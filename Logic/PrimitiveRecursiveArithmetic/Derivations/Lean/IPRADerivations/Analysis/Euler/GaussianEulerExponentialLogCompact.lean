import IPRADerivations.Analysis.Euler.GaussianEulerExponentialNamedLogGrid
import IPRADerivations.Analysis.Integration.GaussianCompactMeshIndependence

/-!
# The compact exponential substitution on logarithmic image grids

The sampler literally sums the named exponential kernel on the
logarithms of the old rational grid nodes, with the actual logarithmic
widths. Its row precision depends on the computed number of cells, so
the accumulated width rounding error vanishes along the same meshes.
The original compact Euler name supplies the limit, with independent
query precisions on the two programs.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerExponentialLogCompact

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerCompactAdditivity (intervalSource)
open GaussianEulerExponentialNamedLogGrid (imageSum observationCost rowNumerator)
open GaussianEulerExponentialSubstitutionCompactBound (majorant)
open GaussianCompactRiemannName (mesh precision quadrature quadrature_index_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm point_at)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def count (t R E T : PTm n) : PTm n := mesh t (GaussianEulerCompactModulus.lipschitz R E T) T
def curvature (R C E T : PTm n) : PTm n := majorant R E T*C*C
def query (t R C E T : PTm n) : PTm n :=
  precision t T+GaussianFastValueCut.exponent
    (observationCost C T (majorant R E T) (GaussianCompactLogarithmBounds.radius E T)*count t R E T) t
def stage (p R C E T : PTm n) : PTm n := GaussianFastValueCut.exponent (curvature R C E T+num 5) p
def diagonalSample (t z R B a C E T : PTm n) : PTm n :=
  imageSum (query t R C E T) z B (count t R E T) a C E
def sample (p z R B a C E T : PTm n) : PTm n := diagonalSample (stage p R C E T) z R B a C E T
def data (z R B a C E T : PTm n) : PTm n := pairT (pairT z R) (pairT (pairT B a) (pairT (pairT C E) T))

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p z R B a C E T : PTm n) :
    Syn.subst σ (sample p z R B a C E T) = sample (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) := by
  simp [sample,diagonalSample,stage,query,count,curvature,observationCost,GaussianEulerExponentialLogGrid.observationCost]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B a C E T : PTm n) :
    Syn.subst σ (data z R B a C E T) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) := by simp [data]

private def fields (p x : PTm n) : Fin 8 → PTm n :=
  ![p,fstT (fstT x),sndT (fstT x),fstT (fstT (sndT x)),sndT (fstT (sndT x)),
    fstT (fstT (sndT (sndT x))),sndT (fstT (sndT (sndT x))),sndT (sndT (sndT x))]
private def body : PTm 8 := sample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
private def reader (p x : PTm n) : PTm n := Syn.subst (fields p x) body
def nameF : PR 2 := PTm.toPR (reader (var 0) (var 1))

private theorem decoded_values (p z R B a C E T : PTm n) (i : Fin 8) :
    Γ ⊢[PRAAx] fields p (data z R B a C E T) i ≐ (![p,z,R,B,a,C,E,T] : Fin 8 → PTm n) i := by
  let x := data z R B a C E T
  have head : Γ ⊢[PRAAx] fstT x ≐ pairT z R := fst_pair _ _
  have tail : Γ ⊢[PRAAx] sndT x ≐ pairT (pairT B a) (pairT (pairT C E) T) := snd_pair _ _
  have mid : Γ ⊢[PRAAx] fstT (sndT x) ≐ pairT B a := (congrFst tail).eqTrans (fst_pair _ _)
  have last : Γ ⊢[PRAAx] sndT (sndT x) ≐ pairT (pairT C E) T := (congrSnd tail).eqTrans (snd_pair _ _)
  have bounds : Γ ⊢[PRAAx] fstT (sndT (sndT x)) ≐ pairT C E := (congrFst last).eqTrans (fst_pair _ _)
  fin_cases i
  · exact .eqRefl _
  · exact (congrFst head).eqTrans (fst_pair _ _)
  · exact (congrSnd head).eqTrans (snd_pair _ _)
  · exact (congrFst mid).eqTrans (fst_pair _ _)
  · exact (congrSnd mid).eqTrans (snd_pair _ _)
  · exact (congrFst bounds).eqTrans (fst_pair _ _)
  · exact (congrSnd bounds).eqTrans (snd_pair _ _)
  · exact (congrSnd last).eqTrans (snd_pair _ _)

theorem name_at (p z R B a C E T : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data z R B a C E T) ≐ sample p z R B a C E T := by
  let x := data z R B a C E T
  have read : Syn.subst (![p,x] : Fin 2 → PTm n) (reader (var 0) (var 1)) = reader p x := by
    unfold reader
    rw [Syn.subst_subst]
    congr 1
    funext i
    fin_cases i <;> simp [fields]
  have first : Γ ⊢[PRAAx] ap2 nameF p x ≐ reader p x := by
    simpa only [nameF,ap2,read] using toPR_eq (Γ := Γ) (reader (var 0) (var 1) : PTm 2) ![p,x]
  have decode : Syn.subst (![p,z,R,B,a,C,E,T] : Fin 8 → PTm n) body = sample p z R B a C E T := by
    simp only [body,subst_sample,Syn.subst_var]
    rfl
  exact first.eqTrans (by simpa only [reader,decode] using Prf.eqCongr body (decoded_values p z R B a C E T))

theorem count_lower (t R E T : PTm n) : Γ ⊢[PRAAx] le (unit t) (count t R E T) := by
  have bigger := GaussianCompactRiemannName.dyadic_monotone (Γ := Γ) t (t+num 6) (le_add_right _ _)
  have meshLower : Γ ⊢[PRAAx] le (unit (t+num 6)) (count t R E T) :=
    le_of_eq_add (d := unit (t+num 6)*GaussianEulerCompactModulus.lipschitz R E T*T*T) (by unfold count mesh; ipra_ring)
  exact le_trans bigger meshLower

private theorem finite_budget (t q N C T M J : PTm n) (hn : Γ ⊢[PRAAx] le (unit t) N)
    (hp : Γ ⊢[PRAAx] le (observationCost C T M J*N*unit t) (unit q)) : Γ ⊢[PRAAx]
    le (rowNumerator q N C T M J*unit t) ((M*C*C+one)*(N*unit q)) := by
  have first := mul_le_mul_right (M*C*C*unit q) hn
  have second := mul_le_mul_right N hp
  exact le_congr (by unfold rowNumerator; ipra_ring) (by ipra_ring) (add_le_add₂ first second)

theorem original_diagonal (t z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) : Γ ⊢[PRAAx]
    distanceBounded (diagonalSample t z R B a C E T)
      (ap2 GaussianEulerCompactAdditivity.nameF t (GaussianEulerCompactAdditivity.data z R B a C E T))
      (curvature R C E T+num 4) (unit t) := by
  let N := count t R E T
  let q := query t R C E T
  let U := unit t
  let M := majorant R E T
  let J := GaussianCompactLogarithmBounds.radius E T
  let S := observationCost C T M J
  let x := GaussianEulerIntegrandName.fixedData z B
  let F := GaussianEulerIntegrandName.evaluatorF
  let L := GaussianEulerCompactModulus.lipschitz R E T
  have hu := unit_positive (Γ := Γ) t
  have hn := le_trans hu (count_lower t R E T)
  have paid : Γ ⊢[PRAAx] le (S*N*U) (unit q) := le_trans
    (GaussianFastValueCut.query_budget _ _) (GaussianCompactRiemannName.dyadic_monotone _ _ (le_add_left _ _))
  have first := distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hn (unit_positive q)) hu
    (finite_budget t q N C T M J (count_lower t R E T) paid)
    (GaussianEulerExponentialNamedLogGrid.original_Euler_log_grid q z R B N a C E T h hn)
  have old := GaussianCompactMeshIndependence.arbitrary_refinement F t q one a C E L T x
    (GaussianEulerCompactAdditivity.compact_input z R B a C E T h) (le_refl one) (le_add_right _ _)
  have aligned := distance_congr (quadrature_index_congr F q _ N a C E x (one_mul N))
    (GaussianCompactRiemannName.name_at F t a C E L T x).eqSymm (.eqRefl _) (.eqRefl _) old
  have finer : Γ ⊢[PRAAx] le (num 3*U) (num 3*unit (t+num 6)) := le_congr (mul_comm _ _) (mul_comm _ _)
    (mul_le_mul_right (num 3) (GaussianCompactRiemannName.dyadic_monotone _ _ (le_add_right _ _)))
  have second := distance_radius_mono _ _ _ _ _ _ (unit_positive (t+num 6)) hu finer aligned
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold curvature; dsimp only [M]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu first second)

theorem original_observations (p q z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B a C E T))
      (ap2 GaussianEulerCompactAdditivity.nameF q (GaussianEulerCompactAdditivity.data z R B a C E T))
      (unit p+unit q) (unit p*unit q) := by
  let t := stage p R C E T
  let A := curvature R C E T
  let P := unit p
  let Q := unit q
  let U := unit t
  have posU := unit_positive (Γ := Γ) t
  have posP := unit_positive (Γ := Γ) p
  have posQ := unit_positive (Γ := Γ) q
  have posD := positive_product _ _ posU posQ
  have pay : Γ ⊢[PRAAx] le ((A+num 5)*P) U := GaussianFastValueCut.query_budget _ _
  have first := distance_radius_mono _ _ _ _ ((A+num 4)*Q) (U*Q) posU posD
    (le_of_eq_add (d := zero) (by ipra_ring)) (original_diagonal t z R B a C E T h)
  have old := point_at GaussianEulerCompactAdditivity.nameF (GaussianEulerCompactAdditivity.data z R B a C E T) t q
    (GaussianEulerCompactAdditivity.name_regular z R B a C E T h)
  have combined := distance_triangle_same _ _ _ _ _ _ posD first old
  have fits : Γ ⊢[PRAAx] le (((A+num 4)*Q+(U+Q))*(P*Q)) ((P+Q)*(U*Q)) := by
    ipra_le (𝔞 Q)^2*sl pay
  exact distance_congr (name_at p z R B a C E T).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ posD (positive_product _ _ posP posQ) fits combined)

theorem original_compact_cross (z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) : Γ ⊢[PRAAx]
    crossEquivalent nameF GaussianEulerCompactAdditivity.nameF (data z R B a C E T) (GaussianEulerCompactAdditivity.data z R B a C E T) := by
  let sh (u : PTm n) := Syn.shift (Syn.shift u)
  have hh : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] intervalSource (sh z) (sh R) (sh B) (sh a) (sh C) (sh E) (sh T) :=
    by simpa only [Fm.shift,GaussianEulerCompactAdditivity.subst_intervalSource,Syn.shift,sh] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,subst_data,GaussianEulerCompactAdditivity.subst_data,Syn.shift,sh] using
    original_observations (var 1) (var 0) (sh z) (sh R) (sh B) (sh a) (sh C) (sh E) (sh T) hh

theorem name_regular (z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) : Γ ⊢[PRAAx]
    pointCN nameF (data z R B a C E T) := by
  have same := original_compact_cross z R B a C E T h
  exact cross_trans _ _ _ _ _ _ same (cross_symm _ _ _ _ same)

theorem actual_exponential_logarithmic_image_compact_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (intervalSource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      crossEquivalent nameF GaussianEulerCompactAdditivity.nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (GaussianEulerCompactAdditivity.data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))) :=
  closeUniv 7 (.impI (original_compact_cross _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerExponentialLogCompact
