import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedFiniteSumFamilySplit
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Families.GaussianNamedFiniteProductFamilyAppend
import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.Folded.GaussianGammaFoldedApproximantBalance
import IPRADerivations.Analysis.Exponential.Names.Identities.GaussianExponentialInverse

/-!
# Exponentiation of an original finite name sum

At every internal prefix, compare the original exponential of the
normalized sum with the original normalized product of exponentials.
The norm of the next row amplifies the preceding error. A primitive
recursive sum of the local costs yields a common geometric bound.
Only that finite observation bound is inducted in the object theory.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianNamedFiniteExponentialFold

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianNameArithmetic (addF addData multiplyF multiplyData multiplyModulus)
open GaussianNameBounds (U sample_bound)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_diagonal_at)
open GaussianNamedFiniteProductFamily (rowF regularRows regular_at family_product_regular)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same distance_radius_mono_same)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (qmul qzero)
open GaussianRationalSyntheticDivision (qone)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (LeanProofs.IPRA.Q.mk Γ t)
local notation "S" => GaussianNamedFiniteSumFamily.nameF
local notation "sd" => GaussianNamedFiniteSumFamily.data
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => GaussianRadiusExponentialName.data

def exponentialBody (f : PR 2) (t : PTm 2) : PTm 2 := exponentialInputData f t
abbrev sumExpF (f : PR 2) (t : PTm 2) : PR 2 := E (S f t)
abbrev productF (f : PR 2) (t : PTm 2) : PR 2 :=
  GaussianNamedFiniteProductName.nameF (rowF (E f) (exponentialBody f t))

def sumExpData (f : PR 2) (t : PTm 2) (i x : PTm n) : PTm n := exponentialInputData (S f t) (sd i x)
def productData (f : PR 2) (t : PTm 2) (i x : PTm n) : PTm n :=
  GaussianNamedFiniteProductFamily.productData (E f) (exponentialBody f t) i x

@[simp] theorem subst_sumExpData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (t : PTm 2) (i x : PTm n) :
    Syn.subst σ (sumExpData f t i x) = sumExpData f t (Syn.subst σ i) (Syn.subst σ x) := by
  simp [sumExpData,exponentialInputData]

@[simp] theorem subst_productData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (t : PTm 2) (i x : PTm n) :
    Syn.subst σ (productData f t i x) = productData f t (Syn.subst σ i) (Syn.subst σ x) := by
  simp [productData,GaussianNamedFiniteProductFamily.productData]

@[simp] theorem exponentialBody_at (f : PR 2) (t : PTm 2) (i x : PTm n) :
    inst2 (exponentialBody f t) i x = exponentialInputData f (inst2 t i x) := by
  simp [exponentialBody,exponentialInputData,inst2]

theorem exponential_rows (f : PR 2) (t : PTm 2) (N x : PTm n) (h : Γ ⊢[PRAAx] regularRows f t N x) :
    Γ ⊢[PRAAx] regularRows (E f) (exponentialBody f t) N x := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] regularRows f t (Syn.shift N) (Syn.shift x) := by simpa [Δ,Fm.shift,Syn.shift] using h.shift.wk
  have r := regular_at f t (Syn.shift N) (Syn.shift x) (var 0) hs (Prf.hyp0 : Δ ⊢[PRAAx] _)
  change Δ ⊢[PRAAx] pointCN (E f) (inst2 (exponentialBody f t) (var 0) (Syn.shift x))
  rw [exponentialBody_at]
  exact GaussianRadiusExponentialName.name_regular f _ _ (exponential_input f _ r)

def localCost (f : PR 2) (t : PTm 2) (i x : PTm n) : PTm n :=
  U (sumExpF f t) (sumExpData f t i x)+U (productF f t) (productData f t i x)
    +two*U (E f) (inst2 (exponentialBody f t) i x)+num 6

def costBody (f : PR 2) (t : PTm 2) : PTm 2 := localCost f t (var 0) (var 1)
def cost (f : PR 2) (t : PTm 2) (N x : PTm n) : PTm n := ap2 (sumF (costBody f t)) N x
def error (C i : PTm n) : PTm n := pw (two*C+one) (succ i)

@[simp] theorem subst_localCost {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (t : PTm 2) (i x : PTm n) :
    Syn.subst σ (localCost f t i x) = localCost f t (Syn.subst σ i) (Syn.subst σ x) := by simp [localCost,two,one,exponentialInputData]
@[simp] theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (t : PTm 2) (N x : PTm n) :
    Syn.subst σ (cost f t N x) = cost f t (Syn.subst σ N) (Syn.subst σ x) := by simp [cost]
@[simp] theorem subst_error {m : ℕ} (σ : Fin n → PTm m) (C i : PTm n) :
    Syn.subst σ (error C i) = error (Syn.subst σ C) (Syn.subst σ i) := by simp [error,two,one]

theorem local_cost_le (f : PR 2) (t : PTm 2) (N i x : PTm n) (h : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] le (localCost f t i x) (cost f t N x) := by
  have term : Γ ⊢[PRAAx] le (inst2 (costBody f t) i x) (cost f t N x) :=
    term_le_sum (costBody f t) (x := x) h
  simpa only [inst2,costBody,subst_localCost,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using term

theorem error_positive (C i : PTm n) : Γ ⊢[PRAAx] le one (error C i) :=
  GaussianFactorBudget.power_positive _ _ (le_congr (.eqRefl _) (add_comm _ _) (le_add_right _ _))

private theorem zero_observation (f : PR 2) (t : PTm 2) (p x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumExpF f t) p (sumExpData f t zero x) ≐ ap2 (productF f t) p (productData f t zero x) := by
  let X := sd zero x
  let R := U (S f t) X
  let s := GaussianRadiusExponentialName.inputPrecision R p
  let y := GaussianNamedFiniteProductFamily.radius (E f) (exponentialBody f t) zero x
  have hs : Γ ⊢[PRAAx] ap2 (S f t) s X ≐ qzero :=
    (GaussianNamedFiniteSumFamily.sample_at f t s zero x).eqTrans (GaussianRationalFiniteSum.sum_zero _ _)
  have a : Γ ⊢[PRAAx] ap2 (sumExpF f t) p (sumExpData f t zero x) ≐ qone := by
    let j := GaussianRadiusExponentialName.index R p
    have start : Γ ⊢[PRAAx] ap2 (sumExpF f t) p (sumExpData f t zero x) ≐
        GaussianRationalPolynomialExponential.scalarSum (ap2 (S f t) s X) j :=
      GaussianRadiusExponentialName.sample_at (S f t) R p X
    have recoded : Γ ⊢[PRAAx] GaussianRationalPolynomialExponential.scalarSum (ap2 (S f t) s X) j ≐
        GaussianRationalPolynomialExponential.scalarSum qzero j :=
      GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody (.eqRefl (succ j)) hs
    exact start.eqTrans (recoded.eqTrans (GaussianGammaCanonicalTailExponential.scalar_zero_point j))
  have b : Γ ⊢[PRAAx] ap2 (productF f t) p (productData f t zero x) ≐ qone :=
    (GaussianNamedFiniteProductName.name_at (rowF (E f) (exponentialBody f t)) p zero y one x).eqTrans
      (GaussianNamedFiniteProduct.sample_zero _ _ _)
  exact a.eqTrans b.eqSymm

private theorem observation_step (F P G : PR 2) (p X X' Y Y' Z d : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F X) (hp : Γ ⊢[PRAAx] pointCN P Y) (hg : Γ ⊢[PRAAx] pointCN G Z)
    (fc : Γ ⊢[PRAAx] crossEquivalent F (multiplyF F G) X' (multiplyData F G X Z))
    (pc : Γ ⊢[PRAAx] crossEquivalent P (multiplyF P G) Y' (multiplyData P G Y Z))
    (ih : Γ ⊢[PRAAx] distanceBounded (ap2 F p X) (ap2 P p Y) d (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F p X') (ap2 P p Y')
      ((U F X+U P Y+two*U G Z+num 6)+U G Z*d) (unit p) := by
  have hU := unit_positive (Γ := Γ) p
  have fx := cross_diagonal_at p fc
  have px := cross_diagonal_at p pc
  have fm := GaussianNameRingLaws.multiply_sample_error F G X Z p hf hg
  have pm := GaussianNameRingLaws.multiply_sample_error P G Y Z p hp hg
  have first := distance_triangle_same _ _ _ _ _ _ hU fx fm
  have last := distance_symmetric _ _ _ _ hU (distance_triangle_same _ _ _ _ _ _ hU px pm)
  have middle := GaussianNameRingLaws.product_left_error (ap2 F p X) (ap2 P p Y) (ap2 G p Z)
    d (unit p) (U G Z) (U P Y) hU ih (sample_bound G Z p hg) (sample_bound P Y p hp)
  have total := distance_triangle_same _ _ _ _ _ _ hU (distance_triangle_same _ _ _ _ _ _ hU first middle) last
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold multiplyModulus; ipra_ring) (.eqRefl _) total

theorem step (f : PR 2) (t : PTm 2) (p N i x : PTm n) (h : Γ ⊢[PRAAx] regularRows f t N x)
    (hi : Γ ⊢[PRAAx] lt i N)
    (ih : Γ ⊢[PRAAx] distanceBounded (ap2 (sumExpF f t) p (sumExpData f t i x))
      (ap2 (productF f t) p (productData f t i x)) (error (cost f t N x) i) (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (sumExpF f t) p (sumExpData f t (succ i) x))
      (ap2 (productF f t) p (productData f t (succ i) x)) (error (cost f t N x) (succ i)) (unit p) := by
  let J := S f t
  let F := sumExpF f t
  let P := productF f t
  let G := E f
  let X := sumExpData f t i x
  let X' := sumExpData f t (succ i) x
  let Y := productData f t i x
  let Y' := productData f t (succ i) x
  let w := inst2 t i x
  let Z := inst2 (exponentialBody f t) i x
  let A := U F X
  let B := U P Y
  let C := U G Z
  let M := cost f t N x
  let d := error M i
  let hU := unit_positive (Γ := Γ) p
  have rows := GaussianNamedFiniteProductFamilyAppend.regular_prefix f t (succ i) N x hi h
  have prior := GaussianNamedFiniteProductFamilyAppend.regular_prefix f t i (succ i) x (le_succ_self i) rows
  have hJ := GaussianNamedFiniteSumFamily.regular f t i x prior
  have hJ' := GaussianNamedFiniteSumFamily.regular f t (succ i) x rows
  have hW := regular_at f t N x i h hi
  have rJ := exponential_input J (sd i x) hJ
  have rJ' := exponential_input J (sd (succ i) x) hJ'
  have rW := exponential_input f w hW
  have hg : Γ ⊢[PRAAx] pointCN G Z := by
    dsimp only [Z]
    rw [exponentialBody_at]
    exact GaussianRadiusExponentialName.name_regular f _ _ rW
  have hf : Γ ⊢[PRAAx] pointCN F X := GaussianRadiusExponentialName.name_regular J _ _ rJ
  have ge := exponential_rows f t (succ i) x rows
  have gp := exponential_rows f t i x prior
  have hb : Γ ⊢[PRAAx] pointCN P Y := family_product_regular _ _ _ _ gp
  have cc := GaussianNamedFiniteSumFamilySplit.append_cross f t i x rows
  have fc : Γ ⊢[PRAAx] crossEquivalent F (multiplyF F G) X' (multiplyData F G X Z) := by
    dsimp only [Z]
    rw [exponentialBody_at]
    exact cross_symm _ _ _ _ (GaussianGammaFoldedApproximantBalance.exponential_product_equivalent J f J _ _ _ _ _ _
      rJ rW rJ' (cross_symm _ _ _ _ cc))
  have pc : Γ ⊢[PRAAx] crossEquivalent P (multiplyF P G) Y' (multiplyData P G Y Z) :=
    GaussianNamedFiniteProductFamilyAppend.family_append_cross G (exponentialBody f t) i x ge
  have total := observation_step F P G p X X' Y Y' Z d hf hb hg fc pc ih
  have cap : Γ ⊢[PRAAx] le (A+B+two*C+num 6) M := local_cost_le f t N i x hi
  have cg : Γ ⊢[PRAAx] le C M := by ipra_le 𝔞(A)+𝔞(B)+𝔞(C)+6+sl cap
  have hd : Γ ⊢[PRAAx] le one d := error_positive M i
  have growth : Γ ⊢[PRAAx] le ((A+B+two*C+num 6)+C*d) (error M (succ i)) := by
    apply le_congr (.eqRefl _) (pw_succ (Γ := Γ) (two*M+one) (succ i)).eqSymm
    change Γ ⊢[PRAAx] le ((A+B+two*C+num 6)+C*d) (d*(two*M+one))
    ipra_le sl cap+𝔞(d)*sl cg+𝔞(M)*sl hd+𝔞(d)
  exact distance_radius_mono_same hU growth total

theorem prefix_error (f : PR 2) (t : PTm 2) (p N i x : PTm n) (h : Γ ⊢[PRAAx] regularRows f t N x)
    (hi : Γ ⊢[PRAAx] le i N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (sumExpF f t) p (sumExpData f t i x))
      (ap2 (productF f t) p (productData f t i x)) (error (cost f t N x) i) (unit p) := by
  let sh (a : PTm n) := Syn.shift a
  let Δ := Γ.map Fm.shift
  let form (k : PTm (n+1)) : Fm PTm (n+1) := le k (sh N) ⟶
    distanceBounded (ap2 (sumExpF f t) (sh p) (sumExpData f t k (sh x)))
      (ap2 (productF f t) (sh p) (productData f t k (sh x))) (error (cost f t (sh N) (sh x)) k) (unit (sh p))
  have h' : Δ ⊢[PRAAx] regularRows f t (sh N) (sh x) := by simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (form (var 0)) := by
    refine PRA.qfInd _ ⟨trivial,trivial⟩ ?_ ?_
    · simp only [form,sh,Fm.subst_imp,subst_le,GaussianRationalMetric.subst_distanceBounded,
        subst_ap2,subst_sumExpData,subst_productData,subst_error,subst_cost,GaussianCoefficientNameBounds.subst_unit,
        Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      refine .impI ?_
      have eq := (zero_observation (Γ := Γ) f t p x).wk (ψ := le zero N)
      have bounds : Γ ⊢[PRAAx] le (zero*unit p) (error (cost f t N x) zero*unit p) :=
        le_congr (zero_mul (unit p)).eqSymm (.eqRefl _) (zero_le _)
      exact distance_congr (.eqRefl _) eq (.eqRefl _) (.eqRefl _)
        (distance_radius_mono _ _ _ _ _ _ (unit_positive p) (unit_positive p) bounds.wk
          (GaussianRationalPowerDifference.distance_refl_zero _ (unit p) (unit_positive p)))
    · simp only [form,sh,Fm.subst_imp,subst_le,GaussianRationalMetric.subst_distanceBounded,
        subst_ap2,subst_sumExpData,subst_productData,subst_error,subst_cost,GaussianCoefficientNameBounds.subst_unit,
        Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let v : PTm (n+1) := var 0
      let Δ' := le (succ v) (sh N) :: form v :: Δ
      have hv : Δ' ⊢[PRAAx] le (succ v) (sh N) := Prf.hyp0
      have prior : Δ' ⊢[PRAAx] form v := Prf.hyp1
      have ih := Prf.impE prior (le_trans (le_succ_self v) hv)
      exact step f t (sh p) (sh N) v (sh x) h'.wk.wk hv ih
  have body : Γ ⊢[PRAAx] le i N ⟶ distanceBounded (ap2 (sumExpF f t) p (sumExpData f t i x))
      (ap2 (productF f t) p (productData f t i x)) (error (cost f t N x) i) (unit p) := by
    simpa only [form,sh,Fm.subst_imp,subst_le,GaussianRationalMetric.subst_distanceBounded,
      subst_ap2,subst_sumExpData,subst_productData,subst_error,subst_cost,GaussianCoefficientNameBounds.subst_unit,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE i
  exact .impE body hi

theorem exponential_product_cross (f : PR 2) (t : PTm 2) (N x : PTm n) (h : Γ ⊢[PRAAx] regularRows f t N x) :
    Γ ⊢[PRAAx] crossEquivalent (sumExpF f t) (productF f t) (sumExpData f t N x) (productData f t N x) := by
  have q := exponential_input (S f t) (sd N x) (GaussianNamedFiniteSumFamily.regular f t N x h)
  have hF : Γ ⊢[PRAAx] pointCN (sumExpF f t) (sumExpData f t N x) :=
    GaussianRadiusExponentialName.name_regular (S f t) _ _ q
  have hG : Γ ⊢[PRAAx] pointCN (productF f t) (productData f t N x) :=
    family_product_regular (E f) (exponentialBody f t) N x (exponential_rows f t N x h)
  apply GaussianNameRingLaws.equivalent_of_envelope (sumExpF f t) (productF f t)
    (sumExpData f t N x) (productData f t N x) (error (cost f t N x) N) hF hG
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] regularRows f t (Syn.shift N) (Syn.shift x) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,subst_sumExpData,subst_productData,subst_error,
    subst_cost] using prefix_error f t (var 0) (Syn.shift N) (Syn.shift N) (Syn.shift x) hs (le_refl _)

theorem actual_original_finite_sum_exponential_product_closed (f : PR 2) (t : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (regularRows f t (var 0) (var 1) ⟶ crossEquivalent (sumExpF f t) (productF f t)
        (sumExpData f t (var 0) (var 1)) (productData f t (var 0) (var 1))) :=
  closeUniv 2 (.impI (exponential_product_cross f t _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedFiniteExponentialFold
