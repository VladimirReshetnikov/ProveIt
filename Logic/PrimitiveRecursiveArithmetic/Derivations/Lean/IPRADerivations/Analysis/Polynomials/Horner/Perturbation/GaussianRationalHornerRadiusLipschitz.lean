import IPRADerivations.Analysis.Polynomials.Horner.Perturbation.GaussianRationalHornerRadiusPerturbation
import IPRADerivations.Analysis.Polynomials.Horner.Perturbation.GaussianRationalHornerLipschitz
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalPowerEnvelope

/-!
# Exact rational-disk point perturbation for actual Horner evaluation

The runtime weighted constant retains the original rational radius U/V.
Actual coefficient, point and coefficient-list codes retain independent
normalization denominators throughout the finite Gaussian arithmetic.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalHornerRadiusLipschitz

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd qmul horner evaluate positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (bound_congr bounded_product)
open LeanProofs.IPRA.Analysis.GaussianRationalHornerPerturbation (bounded_sum_same_den)
open LeanProofs.IPRA.Analysis.GaussianEuclideanResidualRadius (coefficientBounds coefficient_at)
open LeanProofs.IPRA.Analysis.GaussianRationalHornerLipschitz (horner_query_difference_succ)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open LeanProofs.IPRA.Analysis.GaussianRationalPowerEnvelope (weighted weighted_zero weighted_succ subst_weighted)

variable {n : ℕ} {Γ : List (Fm PTm n)}

@[simp] theorem subst_power {m : ℕ} (σ : Fin n → PTm m) (U k : PTm n) :
    Syn.subst σ (pw U k) = pw (Syn.subst σ U) (Syn.subst σ k) := by simp [pw]

def geometricStep : PTm 4 := var 3*var 1+pw (var 2) (var 0)*var 3
def geometricF : PR 3 := recDef (zero : PTm 2) geometricStep
def geometric (U V k : PTm n) : PTm n := ap3 geometricF k U V

ipra_subst geometric

theorem geometric_zero (U V : PTm n) : Γ ⊢[PRAAx] geometric U V zero ≐ zero := by
  have h := rec_zero_vecCons (Γ := Γ) (zero : PTm 2) geometricStep ![U,V]
  simpa [geometric,geometricF,ap3] using h

theorem geometric_succ (U V k : PTm n) : Γ ⊢[PRAAx]
    geometric U V (succ k) ≐ V*geometric U V k+pw U k*V := by
  have h := rec_succ_vecCons (Γ := Γ) (zero : PTm 2) geometricStep k ![U,V]
  simpa [geometric,geometricF,geometricStep,ap3,pw] using h

/-- The literal geometric numerator also satisfies the reverse Horner law. -/
theorem geometric_affine (U V k : PTm n) : Γ ⊢[PRAAx]
    geometric U V (succ k) ≐ U*geometric U V k+pw V (succ k) := by
  have all : Γ ⊢[PRAAx] .all (geometric (Syn.shift U) (Syn.shift V) (succ (var 0)) ≐
      Syn.shift U*geometric (Syn.shift U) (Syn.shift V) (var 0)+pw (Syn.shift V) (succ (var 0))) := by
    ipra_qfind [subst_geometric, subst_power]
    · have g0 := natEq (geometric_zero (Γ := Γ) U V)
      have g1 := natEq (geometric_succ (Γ := Γ) U V zero)
      have p0 := natEq (pw_zero (Γ := Γ) U)
      have p1 := natEq (pw_succ (Γ := Γ) V zero)
      have v0 := natEq (pw_zero (Γ := Γ) V)
      apply deriveNat
      ipra_simps
      rw [g1,g0,p0,p1,v0]
      ring
    · let Δ := (geometric (Syn.shift U) (Syn.shift V) (succ (var 0)) ≐
        Syn.shift U*geometric (Syn.shift U) (Syn.shift V) (var 0)+pw (Syn.shift V) (succ (var 0))) :: Γ.map Fm.shift
      have g0 := natEq (geometric_succ (Γ := Δ) (Syn.shift U) (Syn.shift V) (var 0))
      have g1 := natEq (geometric_succ (Γ := Δ) (Syn.shift U) (Syn.shift V) (succ (var 0)))
      have pu := natEq (pw_succ (Γ := Δ) (Syn.shift U) (var 0))
      have pv := natEq (pw_succ (Γ := Δ) (Syn.shift V) (succ (var 0)))
      have ih := natEq (Prf.hyp0 (Γ := Γ.map Fm.shift) (φ := geometric (Syn.shift U) (Syn.shift V) (succ (var 0)) ≐
        Syn.shift U*geometric (Syn.shift U) (Syn.shift V) (var 0)+pw (Syn.shift V) (succ (var 0))))
      apply deriveNat
      ipra_simps
      linear_combination g1-Groth.ι (IPRA.Q.mk Δ (Syn.shift U))*g0+Groth.ι (IPRA.Q.mk Δ (Syn.shift V))*ih+
        Groth.ι (IPRA.Q.mk Δ (Syn.shift V))*pu-pv
  simpa only [Fm.subst_eq,subst_geometric,ConciseIPRA.PTm.subst_succ,PTm.subst_mul,PTm.subst_add,
    subst_power,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

theorem weighted_affine_step (U V k : PTm n)
    (ih : Γ ⊢[PRAAx] weighted U V (succ k) ≐ U*weighted U V k+geometric U V (succ k)) : Γ ⊢[PRAAx]
    weighted U V (succ (succ k)) ≐ U*weighted U V (succ k)+geometric U V (succ (succ k)) := by
  ipra_lc natEq (weighted_succ (Γ := Γ) U V (succ k))-natEq (geometric_succ (Γ := Γ) U V (succ k))+
    Groth.ι (IPRA.Q.mk Γ V)*natEq ih-
    Groth.ι (IPRA.Q.mk Γ U)*natEq (weighted_succ (Γ := Γ) U V k)+ (Groth.ι (IPRA.Q.mk Γ k)+1)*Groth.ι (IPRA.Q.mk Γ V)*natEq (pw_succ (Γ := Γ) U k)

/-- The independently computed literal weighted power sum satisfies the
exact difference recurrence required by actual Horner evaluation. -/
theorem weighted_affine (U V k : PTm n) : Γ ⊢[PRAAx]
    weighted U V (succ k) ≐ U*weighted U V k+geometric U V (succ k) := by
  have all : Γ ⊢[PRAAx] .all (weighted (Syn.shift U) (Syn.shift V) (succ (var 0)) ≐
      Syn.shift U*weighted (Syn.shift U) (Syn.shift V) (var 0)+geometric (Syn.shift U) (Syn.shift V) (succ (var 0))) := by
    ipra_qfind [subst_weighted, subst_geometric]
    · have w0 := natEq (weighted_zero (Γ := Γ) U V)
      have w1 := natEq (weighted_succ (Γ := Γ) U V zero)
      have g0 := natEq (geometric_zero (Γ := Γ) U V)
      have g1 := natEq (geometric_succ (Γ := Γ) U V zero)
      have p := natEq (pw_zero (Γ := Γ) U)
      apply deriveNat
      ipra_simps
      rw [w1,w0,g1,g0,p]
      ring
    · exact weighted_affine_step _ _ _ Prf.hyp0
  simpa only [Fm.subst_eq,subst_weighted,subst_geometric,ConciseIPRA.PTm.subst_succ,
    PTm.subst_mul,PTm.subst_add,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

def sizeLaw (C w A U V k : PTm n) : Fm PTm n :=
  le k (length C) ⟶ bounded (horner C w k) (A*geometric U V k) (pw V k)

ipra_subst sizeLaw

theorem size_zero (C w A U V : PTm n) : Γ ⊢[PRAAx]
    bounded (horner C w zero) (A*geometric U V zero) (pw V zero) :=
  bound_congr (GaussianRationalHorner.horner_zero C w).eqSymm
    ((congrMul (.eqRefl _) (geometric_zero U V)).eqTrans (mul_zero A)).eqSymm (pw_zero V).eqSymm
    (GaussianMonicResidualRadius.zero_bounded zero one (le_refl _))

theorem size_step (C w A U V k : PTm n)
    (hV : Γ ⊢[PRAAx] le one V) (hC : Γ ⊢[PRAAx] coefficientBounds C A)
    (hw : Γ ⊢[PRAAx] bounded w U V) (hk : Γ ⊢[PRAAx] lt k (length C))
    (ih : Γ ⊢[PRAAx] bounded (horner C w k) (A*geometric U V k) (pw V k)) : Γ ⊢[PRAAx]
    bounded (horner C w (succ k)) (A*geometric U V (succ k)) (pw V (succ k)) := by
  have pk := GaussianPolynomialPerturbation.power_positive (Γ := Γ) V k hV
  have prod := bounded_product _ _ _ _ _ _ pk hV ih hw
  have sum := GaussianRationalReciprocal.bounded_sum _ _ _ _ _ _
    (positive_product _ _ pk hV) (le_refl one) prod (coefficient_at C A k hC hk)
  have num : Γ ⊢[PRAAx] (A*geometric U V k*U)*one+A*(pw V k*V) ≐ A*geometric U V (succ k) := by
    have g := natEq (geometric_affine (Γ := Γ) U V k)
    have p := natEq (pw_succ (Γ := Γ) V k)
    apply deriveNat
    ipra_simps
    rw [g,p]
    ring
  have den : Γ ⊢[PRAAx] (pw V k*V)*one ≐ pw V (succ k) :=
    (by ipra_ring : Γ ⊢[PRAAx] (pw V k*V)*one ≐ pw V k*V).eqTrans (pw_succ V k).eqSymm
  exact bound_congr (GaussianRationalHorner.horner_succ C w k).eqSymm num den sum

/-- True coefficient bounds imply the exact geometric bound for every
actual original rational Horner prefix. -/
theorem size_prefix (C w A U V k : PTm n)
    (hV : Γ ⊢[PRAAx] le one V) (hC : Γ ⊢[PRAAx] coefficientBounds C A)
    (hw : Γ ⊢[PRAAx] bounded w U V) (hk : Γ ⊢[PRAAx] le k (length C)) : Γ ⊢[PRAAx]
    bounded (horner C w k) (A*geometric U V k) (pw V k) := by
  have cShift : Γ.map Fm.shift ⊢[PRAAx] coefficientBounds (Syn.shift C) (Syn.shift A) := by
    simpa only [Fm.shift,GaussianEuclideanResidualRadius.subst_coefficientBounds,Syn.shift] using hC.shift
  have wShift : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift w) (Syn.shift U) (Syn.shift V) := by
    simpa only [Fm.shift,GaussianRationalMetric.subst_bounded,Syn.shift] using hw.shift
  have vShift : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift V) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hV.shift
  have all : Γ ⊢[PRAAx] .all (sizeLaw (Syn.shift C) (Syn.shift w) (Syn.shift A) (Syn.shift U) (Syn.shift V) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,le_QF _ _⟩) [subst_sizeLaw]
    · exact .impI (size_zero C w A U V).wk
    · refine .impI ?_
      exact size_step _ _ _ _ _ _ vShift.wk.wk cShift.wk.wk wShift.wk.wk Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] sizeLaw C w A U V k := by
    simpa only [subst_sizeLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE rule hk

def constantNumerator (N U V A : PTm n) : PTm n := A*weighted U V N

def differenceLaw (C z w N U V A p q k : PTm n) : Fm PTm n := le k N ⟶
  distanceBounded (horner C z (succ k)) (horner C w (succ k)) (constantNumerator k U V A*p) (pw V k*q)

ipra_subst constantNumerator
ipra_subst differenceLaw

theorem difference_zero (C z w U V A p q : PTm n) (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx]
    distanceBounded (horner C z (succ zero)) (horner C w (succ zero)) (constantNumerator zero U V A*p) (pw V zero*q) := by
  have old := GaussianRationalHornerLipschitz.difference_zero C z w U A p q hq
  have num : Γ ⊢[PRAAx] GaussianRationalHornerLipschitz.constant zero U A*p ≐ constantNumerator zero U V A*p := by
    have a := natEq (GaussianRationalHornerLipschitz.weighted_zero (Γ := Γ) U)
    have b := natEq (weighted_zero (Γ := Γ) U V)
    apply deriveNat
    unfold GaussianRationalHornerLipschitz.constant constantNumerator
    ipra_simps
    rw [a,b]
  exact bound_congr (.eqRefl _) num
    ((congrMul (pw_zero V) (.eqRefl _)).eqTrans (one_mul q)).eqSymm old

theorem difference_step (C z w N U V A p q k : PTm n)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N) (hC : Γ ⊢[PRAAx] coefficientBounds C A)
    (hV : Γ ⊢[PRAAx] le one V) (hz : Γ ⊢[PRAAx] bounded z U V) (hw : Γ ⊢[PRAAx] bounded w U V)
    (hq : Γ ⊢[PRAAx] le one q) (hzw : Γ ⊢[PRAAx] distanceBounded z w p q)
    (hk : Γ ⊢[PRAAx] lt k N)
    (ih : Γ ⊢[PRAAx] distanceBounded (horner C z (succ k)) (horner C w (succ k))
      (constantNumerator k U V A*p) (pw V k*q)) : Γ ⊢[PRAAx]
    distanceBounded (horner C z (succ (succ k))) (horner C w (succ (succ k)))
      (constantNumerator (succ k) U V A*p) (pw V (succ k)*q) := by
  have pk := GaussianPolynomialPerturbation.power_positive (Γ := Γ) V k hV
  have pn := GaussianPolynomialPerturbation.power_positive (Γ := Γ) V (succ k) hV
  have prefixIndex : Γ ⊢[PRAAx] le (succ k) (length C) :=
    le_congr (.eqRefl _) hLen.eqSymm (le_trans hk (le_succ_self N))
  have size := size_prefix C w A U V (succ k) hV hC hw prefixIndex
  have first := bounded_product _ _ _ _ _ _ (positive_product _ _ pk hq) hV ih hz
  have den : Γ ⊢[PRAAx] (pw V k*q)*V ≐ pw V (succ k)*q := by
    have p := natEq (pw_succ (Γ := Γ) V k)
    apply deriveNat
    ipra_simps
    rw [p]
    ring
  have first' := bound_congr (.eqRefl _) (.eqRefl _) den first
  have second := bounded_product _ _ _ _ _ _ pn hq size hzw
  have sum := bounded_sum_same_den _ _ _ _ (pw V (succ k)*q) (positive_product _ _ pn hq) first' second
  have num : Γ ⊢[PRAAx] constantNumerator k U V A*p*U+A*geometric U V (succ k)*p ≐ constantNumerator (succ k) U V A*p := by
    have h := natEq (weighted_affine (Γ := Γ) U V k)
    apply deriveNat
    unfold constantNumerator
    ipra_simps
    rw [h]
    ring
  exact bound_congr (horner_query_difference_succ C z w (succ k)).eqSymm num (.eqRefl _) sum

/-- The original coefficient condition yields the exact rational-radius
weighted estimate by QF induction on the actual Horner counter. -/
theorem difference_prefix (C z w N U V A p q k : PTm n)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N) (hC : Γ ⊢[PRAAx] coefficientBounds C A)
    (hV : Γ ⊢[PRAAx] le one V) (hz : Γ ⊢[PRAAx] bounded z U V) (hw : Γ ⊢[PRAAx] bounded w U V)
    (hq : Γ ⊢[PRAAx] le one q) (hzw : Γ ⊢[PRAAx] distanceBounded z w p q)
    (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    distanceBounded (horner C z (succ k)) (horner C w (succ k)) (constantNumerator k U V A*p) (pw V k*q) := by
  have lenShift : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hLen.shift
  have cShift : Γ.map Fm.shift ⊢[PRAAx] coefficientBounds (Syn.shift C) (Syn.shift A) := by
    simpa only [Fm.shift,GaussianEuclideanResidualRadius.subst_coefficientBounds,Syn.shift] using hC.shift
  have vShift : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift V) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hV.shift
  have zShift : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift z) (Syn.shift U) (Syn.shift V) := by
    simpa only [Fm.shift,GaussianRationalMetric.subst_bounded,Syn.shift] using hz.shift
  have wShift : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift w) (Syn.shift U) (Syn.shift V) := by
    simpa only [Fm.shift,GaussianRationalMetric.subst_bounded,Syn.shift] using hw.shift
  have qShift : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift q) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hq.shift
  have zwShift : Γ.map Fm.shift ⊢[PRAAx] distanceBounded (Syn.shift z) (Syn.shift w) (Syn.shift p) (Syn.shift q) := by
    simpa only [Fm.shift,GaussianRationalMetric.subst_distanceBounded,Syn.shift] using hzw.shift
  have all : Γ ⊢[PRAAx] .all (differenceLaw (Syn.shift C) (Syn.shift z) (Syn.shift w) (Syn.shift N)
      (Syn.shift U) (Syn.shift V) (Syn.shift A) (Syn.shift p) (Syn.shift q) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,le_QF _ _⟩) [subst_differenceLaw]
    · exact .impI (difference_zero C z w U V A p q hq).wk
    · refine .impI ?_
      exact difference_step _ _ _ _ _ _ _ _ _ _ lenShift.wk.wk cShift.wk.wk vShift.wk.wk zShift.wk.wk wShift.wk.wk
        qShift.wk.wk zwShift.wk.wk Prf.hyp0 (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] differenceLaw C z w N U V A p q k := by
    simpa only [subst_differenceLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE rule hk

/-- Exact source A sum_(i=1..N) i (U/V)^(i-1) times the original
point distance. The actual sum numerator has the common denominator V^N. -/
theorem evaluation_bound (C z w N U V A p q : PTm n)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N) (hC : Γ ⊢[PRAAx] coefficientBounds C A)
    (hV : Γ ⊢[PRAAx] le one V) (hz : Γ ⊢[PRAAx] bounded z U V) (hw : Γ ⊢[PRAAx] bounded w U V)
    (hq : Γ ⊢[PRAAx] le one q) (hzw : Γ ⊢[PRAAx] distanceBounded z w p q) : Γ ⊢[PRAAx]
    distanceBounded (evaluate C z) (evaluate C w) (constantNumerator N U V A*p) (pw V N*q) :=
  bound_congr (qsub_congr
    (congrAp3 GaussianRationalHorner.hornerF hLen.eqSymm (.eqRefl _) (.eqRefl _))
    (congrAp3 GaussianRationalHorner.hornerF hLen.eqSymm (.eqRefl _) (.eqRefl _))) (.eqRefl _) (.eqRefl _)
      (difference_prefix C z w N U V A p q N hLen hC hV hz hw hq hzw (le_refl _))

/-! The actual rational weighted constant and a single uniform PR9 result
retain their computed numerator, denominator and literal evaluation difference. -/
def constant (N U V A : PTm n) : PTm n :=
  RationalIntegerNormalization.normalize (ZT.ofNat (constantNumerator N U V A)) (pw V N)
def constantF : PR 4 := PTm.toPR (constant (var 0) (var 1) (var 2) (var 3))

ipra_subst constant

theorem constant_represents (N U V A : PTm n) (hV : Γ ⊢[PRAAx] le one V) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (constant N U V A) (ZT.ofNat (constantNumerator N U V A)) (pw V N) :=
  RationalIntegerNormalization.normalize_preserves_value _ _ (GaussianPolynomialPerturbation.power_positive _ _ hV)

theorem constant_program_at (N U V A : PTm n) : Γ ⊢[PRAAx]
    PTm.app constantF ![N,U,V,A] ≐ constant N U V A := by
  simpa [constantF] using toPR_eq (Γ := Γ) (constant (var 0) (var 1) (var 2) (var 3) : PTm 4) ![N,U,V,A]

def output (C z w N U V A p q : PTm n) : PTm n := pairT (qsub (evaluate C z) (evaluate C w))
  (pairT (constantNumerator N U V A*p) (pw V N*q))
def outputF : PR 9 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
def run (C z w N U V A p q : PTm n) : PTm n := PTm.app outputF ![C,z,w,N,U,V,A,p,q]

ipra_subst output
ipra_subst run

theorem program_at (C z w N U V A p q : PTm n) : Γ ⊢[PRAAx]
    run C z w N U V A p q ≐ output C z w N U V A p q := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) : PTm 9) ![C,z,w,N,U,V,A,p,q]

theorem output_value (C z w N U V A p q : PTm n) : Γ ⊢[PRAAx]
    fstT (run C z w N U V A p q) ≐ qsub (evaluate C z) (evaluate C w) :=
  (program_at C z w N U V A p q).fstE
theorem output_numerator (C z w N U V A p q : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run C z w N U V A p q)) ≐ constantNumerator N U V A*p :=
  (program_at C z w N U V A p q).sndE.fstE
theorem output_denominator (C z w N U V A p q : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run C z w N U V A p q)) ≐ pw V N*q :=
  (program_at C z w N U V A p q).sndE.sndE

theorem program_certificate (C z w N U V A p q : PTm n)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N) (hC : Γ ⊢[PRAAx] coefficientBounds C A)
    (hV : Γ ⊢[PRAAx] le one V) (hz : Γ ⊢[PRAAx] bounded z U V) (hw : Γ ⊢[PRAAx] bounded w U V)
    (hq : Γ ⊢[PRAAx] le one q) (hzw : Γ ⊢[PRAAx] distanceBounded z w p q) : Γ ⊢[PRAAx]
    le one (sndT (sndT (run C z w N U V A p q))) ⋏
      bounded (fstT (run C z w N U V A p q)) (fstT (sndT (run C z w N U V A p q))) (sndT (sndT (run C z w N U V A p q))) :=
  .andI (le_congr (.eqRefl _) (output_denominator C z w N U V A p q).eqSymm
      (positive_product _ _ (GaussianPolynomialPerturbation.power_positive _ _ hV) hq))
    (bound_congr (output_value C z w N U V A p q).eqSymm (output_numerator C z w N U V A p q).eqSymm
      (output_denominator C z w N U V A p q).eqSymm (evaluation_bound C z w N U V A p q hLen hC hV hz hw hq hzw))

theorem rational_disk_recurrences_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((geometric (var 0) (var 1) (succ (var 2)) ≐ var 0*geometric (var 0) (var 1) (var 2)+pw (var 1) (succ (var 2))) ⋏
      (weighted (var 0) (var 1) (succ (var 2)) ≐ var 0*weighted (var 0) (var 1) (var 2)+geometric (var 0) (var 1) (succ (var 2)))) :=
  closeUniv 3 (.andI (geometric_affine _ _ _) (weighted_affine _ _ _))

theorem rational_disk_horner_size_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 4) ⟶ coefficientBounds (var 0) (var 2) ⟶ bounded (var 1) (var 3) (var 4) ⟶ le (var 5) (length (var 0)) ⟶
      bounded (horner (var 0) (var 1) (var 5)) (var 2*geometric (var 3) (var 4) (var 5)) (pw (var 4) (var 5))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (size_prefix _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem rational_disk_horner_lipschitz_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (length (var 0) ≐ succ (var 3) ⟶ coefficientBounds (var 0) (var 6) ⟶ le one (var 5) ⟶
      bounded (var 1) (var 4) (var 5) ⟶ bounded (var 2) (var 4) (var 5) ⟶ le one (var 8) ⟶
      distanceBounded (var 1) (var 2) (var 7) (var 8) ⟶
        distanceBounded (evaluate (var 0) (var 1)) (evaluate (var 0) (var 2))
          (constantNumerator (var 3) (var 4) (var 5) (var 6)*var 7) (pw (var 5) (var 3)*var 8)) := by
  apply closeUniv 9
  refine .impI (.impI (.impI (.impI (.impI (.impI (.impI ?_))))))
  exact evaluation_bound _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem rational_disk_horner_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ≐
      output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) := closeUniv 9 (program_at _ _ _ _ _ _ _ _ _)

theorem rational_disk_horner_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (length (var 0) ≐ succ (var 3) ⟶ coefficientBounds (var 0) (var 6) ⟶ le one (var 5) ⟶
      bounded (var 1) (var 4) (var 5) ⟶ bounded (var 2) (var 4) (var 5) ⟶ le one (var 8) ⟶
      distanceBounded (var 1) (var 2) (var 7) (var 8) ⟶
        (le one (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))))) ⋏
          bounded (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
            (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))))
            (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))))) := by
  apply closeUniv 9
  refine .impI (.impI (.impI (.impI (.impI (.impI (.impI ?_))))))
  exact program_certificate _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

end LeanProofs.IPRA.Analysis.GaussianRationalHornerRadiusLipschitz
