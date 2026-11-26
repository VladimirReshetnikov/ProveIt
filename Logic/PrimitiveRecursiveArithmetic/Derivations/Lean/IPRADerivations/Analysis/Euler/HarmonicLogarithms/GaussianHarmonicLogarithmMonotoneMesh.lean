import IPRADerivations.Analysis.Euler.HarmonicLogarithms.GaussianHarmonicLogarithmName

/-!
# Exact monotonicity of the ordered harmonic logarithm mesh

On an ordered positive interval, each refinement improves the
right-endpoint reciprocal sum. Thus the actual harmonic logarithm
observations increase with their dyadic precision.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianHarmonicLogarithmMonotoneMesh

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianHarmonicLogarithmName (clock sample observation)
open Products (fact)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalHarmonicInterval (common interval horizon numerator)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem interval_refinement_order (a b Q E : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hba : Γ ⊢[PRAAx] le b a) (hQ : Γ ⊢[PRAAx] le one Q)
    (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    rationalLE (interval a b Q) (interval a b (E*Q)) := by
  let L := E*horizon a b Q
  let F := fact L
  let U := Q*a
  let V := Q*b
  have hu : Γ ⊢[PRAAx] le one V := RationalAlgebra.positive_product hQ hb
  have order : Γ ⊢[PRAAx] le V U := le_mul_mono (le_refl Q) hba
  have low : Γ ⊢[PRAAx] le (horizon a b Q) L := by
    dsimp [L]
    ipra_le 𝔞 (horizon a b Q)*sl hE
  have high : Γ ⊢[PRAAx] le (horizon a b (E*Q)) L :=
    le_congr (by dsimp [horizon,L]; ipra_ring) (.eqRefl _) (le_refl _)
  have bound : Γ ⊢[PRAAx] le (E*U) L := le_mul_mono (le_refl E) (RationalHarmonicInterval.left_horizon a b Q)
  have signed := (GammaEulerMesh.synchronous_cleared V U E L hu order hE bound).andE₁
  have eU : Γ ⊢[PRAAx] S ((E*Q)*a) F ≐ S (E*U) F :=
    congrAp2 (sumF hB) (by dsimp [U]; ipra_ring) (.eqRefl _)
  have eV : Γ ⊢[PRAAx] S ((E*Q)*b) F ≐ S (E*V) F :=
    congrAp2 (sumF hB) (by dsimp [V]; ipra_ring) (.eqRefl _)
  have hF := GammaEulerMesh.factorial_positive (Γ := Γ) L
  apply rationalLE_congr (RationalHarmonicInterval.at_common a b Q L low)
    (RationalHarmonicInterval.at_common a b (E*Q) L high)
  apply RationalArithmetic.order_of_representations _ _ (numerator a b Q L) (numerator a b (E*Q) L) F F
    (RationalHarmonicInterval.common_value _ _ _ _) (RationalHarmonicInterval.common_value _ _ _ _) hF hF
  apply zle_of_toZ (F*monus (S V F+S (E*U) F) (S U F+S (E*V) F))
  have first := natEq eU
  have second := natEq eV
  have e := natEq (eq_add_of_le signed)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [numerator,ZT.toZ]
  ipra_simps
  linear_combination 𝔞 F*(second-first-e)

theorem sample_order (a b p t : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hba : Γ ⊢[PRAAx] le b a) (hpt : Γ ⊢[PRAAx] le p t) : Γ ⊢[PRAAx]
    rationalLE (fstT (sample p a b)) (fstT (sample t a b)) := by
  let d := monus t p
  let E := pw two d
  let Q := GammaEulerConstantName.mesh (clock p)
  let T := GammaEulerConstantName.mesh (clock t)
  have clockEq : Γ ⊢[PRAAx] clock t ≐ clock p+d := by
    have h := natEq (eq_add_of_le hpt)
    apply deriveNat
    unfold clock d
    ipra_simps
    linear_combination h
  have meshEq : Γ ⊢[PRAAx] T ≐ E*Q := by
    have step := natEq ((congrAp2 powF clockEq (.eqRefl two)).eqTrans (pw_add two (clock p) d))
    apply deriveNat
    unfold T Q E GammaEulerConstantName.mesh GammaEulerConstantName.unit
    ipra_simps
    linear_combination 4*step
  have code := Prf.eqCongr (Ax := PRAAx) (Γ := Γ)
    (fstT (RationalGaussianEmbedding.embed (interval (var 0) (var 1) (var 2))) : PTm 3)
    (σ := ![a,b,E*Q]) (σ' := ![a,b,T])
    (fun i => by
      fin_cases i
      · exact .eqRefl _
      · exact .eqRefl _
      · exact meshEq.eqSymm)
  have read : Γ ⊢[PRAAx] fstT (RationalGaussianEmbedding.embed (interval a b (E*Q))) ≐ fstT (sample t a b) := by
    have eq : Γ ⊢[PRAAx] fstT (RationalGaussianEmbedding.embed (interval a b (E*Q))) ≐
        fstT (RationalGaussianEmbedding.embed (interval a b T)) := by
      simpa only [subst_fstT,RationalGaussianEmbedding.subst_embed,RationalHarmonicInterval.subst_interval,
        Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] using code
    exact eq.eqTrans (congrFst (GaussianHarmonicLogarithmName.sample_at t a b)).eqSymm
  have low : Γ ⊢[PRAAx] le one Q := GammaEulerConstantName.mesh_positive (clock p)
  have positive : Γ ⊢[PRAAx] le one E := GaussianFactorBudget.power_positive two d (le_succ_self one)
  have h := interval_refinement_order a b Q E hb hba low positive
  have scalar_at (P : PTm n) : Γ ⊢[PRAAx] fstT (RationalGaussianEmbedding.embed (interval a b P)) ≐ interval a b P :=
    (fst_pair _ _).eqTrans (RationalNormalForm.normalize_fixed_point _ (RationalHarmonicInterval.common_canonical a b P _))
  exact rationalLE_congr
    ((scalar_at Q).eqSymm.eqTrans (congrFst (GaussianHarmonicLogarithmName.sample_at p a b)).eqSymm)
    ((scalar_at (E*Q)).eqSymm.eqTrans read) h

end LeanProofs.IPRA.Analysis.GaussianHarmonicLogarithmMonotoneMesh
