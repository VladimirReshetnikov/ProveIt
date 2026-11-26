import IPRADerivations.Analysis.Polynomials.RationalPolynomialMultiplicationMatrixGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.RationalPolynomialDeterminantTransport
import IPRADerivations.Analysis.RationalArithmetic.RationalCurvePointsGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.RationalPolynomialNonvanishing
import IPRADerivations.Analysis.RationalArithmetic.GaussianNormFiniteZeroBound

/-!
# The actual rational norm and its sharp finite point bound

Original rational coefficients produce the actual multiplication matrix,
whose original rational determinant is passed to the original coefficient
test. Its bounded entries determine the Gaussian coefficient transport.
The rational zero list retains its cardinality and both point predicates,
so the proved Gaussian norm bound gives the original rational result.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPolynomialMonicNorm

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalGaussianEmbedding (embed scalarZero)
open RationalPolynomialMultiplicationMatrixGaussianEmbedding (matrix matrix_entry_embedding)
open RationalPolynomialDeterminantTransport (matrixEmbedded)
open RationalPolynomialBuffersGaussianEmbedding (embeddedEntries)
open RationalPolynomialMonicCompanionGaussianEmbedding (embedded_congr)
open GaussianPolynomialMonicNorm (degreeBound width)
open GaussianPolynomialDeterminantTerms (cell)
open GaussianNormFiberDivisibility (sourceOriginal)
open GaussianRationalFiberGrouping (abscissa)
open RationalCurvePointsGaussianEmbedding (points points_length abscissa_at)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

local notation "embedRows" => RationalRowSpanGaussianEmbedding.matrix

variable {n : ℕ} {Γ : List (Fm PTm n)}

def norm (F G m a c : PTm n) : PTm n :=
  RationalPolynomialDeterminantGaussianEmbedding.determinant (matrix F G m a c) m (width m a c)
def flag (F G m a c : PTm n) : PTm n :=
  RationalPolynomialDegreeGaussianEmbedding.flag (norm F G m a c) (degreeBound m a c)
def degree (F G m a c : PTm n) : PTm n :=
  RationalPolynomialDegreeGaussianEmbedding.degree (norm F G m a c) (degreeBound m a c)
def input (F G m a c L : PTm n) : Fm PTm n := GaussianPolynomialMonicNorm.input F G m a c ⋏
  (RationalCurvePointsGaussianEmbedding.sourceInput F G m L ⋏ flag F G m a c ≐ one)

@[simp] theorem subst_norm {l : ℕ} (σ : Fin n → PTm l) (F G m a c : PTm n) :
    Syn.subst σ (norm F G m a c) = norm (Syn.subst σ F) (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) := by
  simp [norm]
@[simp] theorem subst_flag {l : ℕ} (σ : Fin n → PTm l) (F G m a c : PTm n) :
    Syn.subst σ (flag F G m a c) = flag (Syn.subst σ F) (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) := by
  simp [flag]
@[simp] theorem subst_degree {l : ℕ} (σ : Fin n → PTm l) (F G m a c : PTm n) :
    Syn.subst σ (degree F G m a c) = degree (Syn.subst σ F) (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) := by
  simp [degree]

theorem matrix_embedded (F G m a c : PTm n) (h : Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F G m a c) :
    Γ ⊢[PRAAx] matrixEmbedded (matrix F G m a c)
      (GaussianPolynomialMonicNorm.matrix (embedRows F m (succ c)) (embedRows G m (succ a)) m a c) m (width m a c) := by
  refine .allI (.impI (.allI (.impI (.allI (.impI ?_)))))
  let F' := Syn.shift (Syn.shift (Syn.shift F))
  let G' := Syn.shift (Syn.shift (Syn.shift G))
  let M := Syn.shift (Syn.shift (Syn.shift m))
  let A := Syn.shift (Syn.shift (Syn.shift a))
  let C := Syn.shift (Syn.shift (Syn.shift c))
  let Δ := lt (var 0) (succ (width M A C)) :: lt (var 1) M :: lt (var 2) M ::
    ((Γ.map Fm.shift).map Fm.shift).map Fm.shift
  have source : Δ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F' G' M A C := by
    simpa [Δ,F',G',M,A,C,Fm.shift,Syn.shift,one] using h.shift.shift.shift.wk.wk.wk
  have hs : Δ ⊢[PRAAx] le (var 0) (width M A C) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have sample := matrix_entry_embedding F' G' M A C (var 2) (var 1) (var 0) (.andE₁ source)
    (.andE₁ (.andE₂ source)) (.andE₂ (.andE₂ source)) Prf.hyp1.wk Prf.hyp1 hs
  simpa [Δ,F',G',M,A,C,Fm.shift,Syn.shift,GaussianPolynomialMonicNorm.matrix,cell] using sample

theorem norm_length (F G m a c : PTm n) : Γ ⊢[PRAAx] length (norm F G m a c) ≐ succ (degreeBound m a c) :=
  RationalPolynomialDeterminantGaussianEmbedding.determinant_length _ _ _

theorem norm_entries (F G m a c : PTm n) (h : Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F G m a c) : Γ ⊢[PRAAx]
    embeddedEntries (norm F G m a c) (sourceOriginal (embedRows F m (succ c)) (embedRows G m (succ a)) m a c)
      (succ (degreeBound m a c)) :=
  embedded_congr (.eqRefl _) (GaussianPolynomialMonicNorm.returned_norm _ _ _ _ _).eqSymm
    (RationalPolynomialDeterminantTransport.determinant_transport _ _ _ _ (matrix_embedded F G m a c h))

theorem evaluation_embedding (F G m a c x : PTm n) (h : Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F G m a c) : Γ ⊢[PRAAx]
    embed (RationalPolynomialGaussianEmbedding.evaluate (norm F G m a c) x) ≐
      GaussianRationalHorner.evaluate (sourceOriginal (embedRows F m (succ c)) (embedRows G m (succ a)) m a c) (embed x) :=
  RationalPolynomialBuffersGaussianEmbedding.evaluation_transport _ _ _ _ (norm_length F G m a c)
    (GaussianPolynomialMonicNorm.returned_length _ _ _ _ _) (norm_entries F G m a c h)

theorem flag_embedding (F G m a c : PTm n) (h : Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F G m a c) : Γ ⊢[PRAAx]
    flag F G m a c ≐ GaussianRationalPolynomialDegree.flag
      (sourceOriginal (embedRows F m (succ c)) (embedRows G m (succ a)) m a c) (degreeBound m a c) :=
  RationalPolynomialDegreeGaussianEmbedding.flag_conjugacy _ _ _ (norm_entries F G m a c h)

theorem degree_embedding (F G m a c : PTm n) (h : Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F G m a c) : Γ ⊢[PRAAx]
    degree F G m a c ≐ GaussianRationalPolynomialDegree.degree
      (sourceOriginal (embedRows F m (succ c)) (embedRows G m (succ a)) m a c) (degreeBound m a c) :=
  RationalPolynomialDegreeGaussianEmbedding.degree_conjugacy _ _ _ (norm_entries F G m a c h)

theorem gaussian_input (F G m a c : PTm n) (h : Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F G m a c) :
    Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input (embedRows F m (succ c)) (embedRows G m (succ a)) m a c :=
  .andI (.andE₁ h) (.andI (RationalBivariateGaussianEmbedding.embedded_row_shape F m c)
    (RationalBivariateGaussianEmbedding.embedded_row_shape G m a))

theorem gaussian_points (F G m a c L : PTm n)
    (h : Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F G m a c)
    (hp : Γ ⊢[PRAAx] RationalCurvePointsGaussianEmbedding.sourceInput F G m L) : Γ ⊢[PRAAx]
    GaussianRationalCurveFibers.sourceInput (embedRows F m (succ c)) (embedRows G m (succ a)) m (points L) :=
  RationalCurvePointsGaussianEmbedding.mapped_source F G m a c L (.andE₁ (.andE₂ h)) (.andE₂ (.andE₂ h)) hp

theorem finite_zero_bound (F G m a c L : PTm n) (h : Γ ⊢[PRAAx] input F G m a c L) :
    Γ ⊢[PRAAx] le (length L) (degree F G m a c) := by
  have hNorm := Prf.andE₁ h
  have hPoints := gaussian_points F G m a c L hNorm (.andE₁ (.andE₂ h))
  have nonzero := (flag_embedding F G m a c hNorm).eqSymm.eqTrans (Prf.andE₂ (Prf.andE₂ h))
  have bound := GaussianNormFiniteZeroBound.finite_norm_zero_bound
    (embedRows F m (succ c)) (embedRows G m (succ a)) m a c (points L) zero
    (.andI (gaussian_input F G m a c hNorm) (.andI hPoints nonzero))
  exact le_congr (points_length L) (degree_embedding F G m a c hNorm).eqSymm bound

theorem finite_zero_bound_of_nonzero (F G m a c L : PTm n)
    (hn : Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F G m a c)
    (hp : Γ ⊢[PRAAx] RationalCurvePointsGaussianEmbedding.sourceInput F G m L)
    (hs : Γ ⊢[PRAAx] RationalPolynomialNonvanishing.nonzeroCoefficients (norm F G m a c) (degreeBound m a c)) :
    Γ ⊢[PRAAx] le (length L) (degree F G m a c) :=
  finite_zero_bound F G m a c L (.andI hn (.andI hp (RationalPolynomialNonvanishing.flag_of_nonzero _ _ hs)))

theorem finite_zero_width_bound (F G m a c L : PTm n) (h : Γ ⊢[PRAAx] input F G m a c L) :
    Γ ⊢[PRAAx] le (length L) (degreeBound m a c) := by
  have hNorm := Prf.andE₁ h
  exact le_trans (finite_zero_bound F G m a c L h)
    (le_congr (degree_embedding F G m a c hNorm).eqSymm (.eqRefl _) (GaussianRationalPolynomialDegree.degree_le _ _))

theorem original_point_norm_zero (F G m a c L i : PTm n)
    (hn : Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F G m a c)
    (hp : Γ ⊢[PRAAx] RationalCurvePointsGaussianEmbedding.sourceInput F G m L)
    (hi : Γ ⊢[PRAAx] lt i (length L)) : Γ ⊢[PRAAx]
    RationalArgmin.rationalEq (RationalPolynomialGaussianEmbedding.evaluate (norm F G m a c) (abscissa L i)) scalarZero := by
  have hz := GaussianNormFiniteZeroBound.original_point_norm_zero
    (embedRows F m (succ c)) (embedRows G m (succ a)) m a c (points L) zero i
    (gaussian_input F G m a c hn) (gaussian_points F G m a c L hn hp)
    (lt_congr (.eqRefl _) (points_length L).eqSymm hi)
  exact (RationalGaussianEmbedding.zero_iff _).iffMp
    ((evaluation_embedding F G m a c (abscissa L i) hn).eqTrans
      ((GaussianRationalMonicReduction.evaluate_congr (.eqRefl _) (abscissa_at L i hi).eqSymm).eqTrans hz))

def output (F G m a c : PTm n) : PTm n := pairT (norm F G m a c) (pairT (flag F G m a c) (degree F G m a c))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (F G m a c : PTm n) : PTm n := PTm.app outputF ![F,G,m,a,c]

@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (F G m a c : PTm n) :
    Syn.subst σ (output F G m a c) = output (Syn.subst σ F) (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) := by
  simp [output]

theorem program_at (F G m a c : PTm n) : Γ ⊢[PRAAx] run F G m a c ≐ output F G m a c := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![F,G,m,a,c]
theorem returned_norm (F G m a c : PTm n) : Γ ⊢[PRAAx] fstT (run F G m a c) ≐ norm F G m a c :=
  (congrFst (program_at _ _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_flag (F G m a c : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run F G m a c)) ≐ flag F G m a c :=
  (congrFst ((congrSnd (program_at _ _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_degree (F G m a c : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run F G m a c)) ≐ degree F G m a c :=
  (congrSnd ((congrSnd (program_at _ _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_zero_bound (F G m a c L : PTm n)
    (hn : Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F G m a c)
    (hp : Γ ⊢[PRAAx] RationalCurvePointsGaussianEmbedding.sourceInput F G m L)
    (hf : Γ ⊢[PRAAx] fstT (sndT (run F G m a c)) ≐ one) : Γ ⊢[PRAAx]
    le (length L) (sndT (sndT (run F G m a c))) :=
  le_congr (.eqRefl _) (returned_degree _ _ _ _ _).eqSymm (finite_zero_bound F G m a c L
    (.andI hn (.andI hp ((returned_flag _ _ _ _ _).eqSymm.eqTrans hf))))

theorem actual_rational_monic_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianPolynomialMonicNorm.input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      embeddedEntries (norm (var 0) (var 1) (var 2) (var 3) (var 4))
        (sourceOriginal (embedRows (var 0) (var 2) (succ (var 4))) (embedRows (var 1) (var 2) (succ (var 3)))
          (var 2) (var 3) (var 4)) (succ (degreeBound (var 2) (var 3) (var 4)))) :=
  closeUniv 5 (.impI (norm_entries _ _ _ _ _ Prf.hyp0))

theorem actual_rational_norm_zero_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      le (length (var 5)) (degree (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 6 (.impI (finite_zero_bound _ _ _ _ _ _ Prf.hyp0))

theorem actual_rational_norm_count_of_nonzero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (GaussianPolynomialMonicNorm.input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      RationalCurvePointsGaussianEmbedding.sourceInput (var 0) (var 1) (var 2) (var 5) ⟶
      RationalPolynomialNonvanishing.nonzeroCoefficients (norm (var 0) (var 1) (var 2) (var 3) (var 4))
        (degreeBound (var 2) (var 3) (var 4)) ⟶
      le (length (var 5)) (degree (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 6 (.impI (.impI (.impI (finite_zero_bound_of_nonzero _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem actual_rational_point_norm_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (GaussianPolynomialMonicNorm.input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      RationalCurvePointsGaussianEmbedding.sourceInput (var 0) (var 1) (var 2) (var 5) ⟶
      lt (var 6) (length (var 5)) ⟶ RationalArgmin.rationalEq
        (RationalPolynomialGaussianEmbedding.evaluate (norm (var 0) (var 1) (var 2) (var 3) (var 4)) (abscissa (var 5) (var 6))) scalarZero) :=
  closeUniv 7 (.impI (.impI (.impI (original_point_norm_zero _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem actual_rational_norm_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)

theorem actual_returned_rational_norm_zero_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (GaussianPolynomialMonicNorm.input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      RationalCurvePointsGaussianEmbedding.sourceInput (var 0) (var 1) (var 2) (var 5) ⟶
      fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))) ≐ one ⟶
        le (length (var 5)) (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))) :=
  closeUniv 6 (.impI (.impI (.impI (returned_zero_bound _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.RationalPolynomialMonicNorm
