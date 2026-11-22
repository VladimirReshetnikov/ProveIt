import IPRADerivations.Analysis.RationalCubeGrid
import IPRADerivations.Analysis.GapRemoval

/-!
# Actual sampled minima on the numerical dyadic cube grid

The fixed source sampler and modulus are program syntax. Dimensions, query
precisions and persistent data are numerical. The actual earliest rational
argmin runs over the exact positive grid count. Original coherence and
continuity contracts will supply the source quarter-budget inequalities;
no minimum, regularity or infimum output law is an input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalCubeMinimum

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalCubeGrid (cube point grid count scale radix fraction)
open RationalArgmin (rationalLE rationalLE_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)
open LeanProofs.IPRA.PTm (pred monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

@[simp] private theorem up_two {a b : ℕ} (σ : Fin (a+2) → PTm b) : Syn.up σ 2 = Syn.shift (σ 1) := Syn.up_succ σ 1
@[simp] private theorem up_three {a b : ℕ} (σ : Fin (a+3) → PTm b) : Syn.up σ 3 = Syn.shift (σ 2) := Syn.up_succ σ 2
@[simp] private theorem up_four {a b : ℕ} (σ : Fin (a+4) → PTm b) : Syn.up σ 4 = Syn.shift (σ 3) := Syn.up_succ σ 3

def presentedCube (y d : PTm n) : Fm PTm n := cube y d ⋏ .all (lt (var 0) (Syn.shift d) ⟶
  RationalNormalForm.wellFormed (entry (Syn.shift y) (var 0)))
def precision (k : PTm n) : PTm n := succ (succ k)
def mesh (mu : PR 2) (k x : PTm n) : PTm n := ap2 mu (precision k) x
def horizon (mu : PR 2) (d k x : PTm n) : PTm n := count d (mesh mu k x)
def data (d k x : PTm n) : PTm n := pairT d (pairT k x)
def sample (A : PR 3) (y p x : PTm n) : PTm n := ap3 A y p x
def score (A : PR 3) (mu : PR 2) (d k x i : PTm n) : PTm n := sample A (point d (mesh mu k x) i) (precision k) x
def scoreBody (A : PR 3) (mu : PR 2) : PTm 2 := score A mu (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def scoreF (A : PR 3) (mu : PR 2) : PR 2 := PTm.toPR (scoreBody A mu)
def index (A : PR 3) (mu : PR 2) (d k x : PTm n) : PTm n :=
  RationalArgmin.selected (scoreF A mu) (pred (horizon mu d k x)) (data d k x)
def minimizer (A : PR 3) (mu : PR 2) (d k x : PTm n) : PTm n := point d (mesh mu k x) (index A mu d k x)
def minimum (A : PR 3) (mu : PR 2) (d k x : PTm n) : PTm n := sample A (minimizer A mu d k x) (precision k) x

@[simp] theorem subst_presentedCube {q : ℕ} (σ : Fin n → PTm q) (y d : PTm n) :
    (presentedCube y d).subst σ = presentedCube (Syn.subst σ y) (Syn.subst σ d) := by
  simp [presentedCube,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_precision {q : ℕ} (σ : Fin n → PTm q) (k : PTm n) : Syn.subst σ (precision k) = precision (Syn.subst σ k) := by simp [precision]
@[simp] theorem subst_mesh {q : ℕ} (σ : Fin n → PTm q) (mu : PR 2) (k x : PTm n) :
    Syn.subst σ (mesh mu k x) = mesh mu (Syn.subst σ k) (Syn.subst σ x) := by simp [mesh]
@[simp] theorem subst_horizon {q : ℕ} (σ : Fin n → PTm q) (mu : PR 2) (d k x : PTm n) :
    Syn.subst σ (horizon mu d k x) = horizon mu (Syn.subst σ d) (Syn.subst σ k) (Syn.subst σ x) := by simp [horizon]
@[simp] theorem subst_data {q : ℕ} (σ : Fin n → PTm q) (d k x : PTm n) :
    Syn.subst σ (data d k x) = data (Syn.subst σ d) (Syn.subst σ k) (Syn.subst σ x) := by simp [data]
@[simp] theorem subst_sample {q : ℕ} (σ : Fin n → PTm q) (A : PR 3) (y p x : PTm n) :
    Syn.subst σ (sample A y p x) = sample A (Syn.subst σ y) (Syn.subst σ p) (Syn.subst σ x) := by simp [sample]
@[simp] theorem subst_score {q : ℕ} (σ : Fin n → PTm q) (A : PR 3) (mu : PR 2) (d k x i : PTm n) :
    Syn.subst σ (score A mu d k x i) = score A mu (Syn.subst σ d) (Syn.subst σ k) (Syn.subst σ x) (Syn.subst σ i) := by simp [score]
@[simp] theorem subst_index {q : ℕ} (σ : Fin n → PTm q) (A : PR 3) (mu : PR 2) (d k x : PTm n) :
    Syn.subst σ (index A mu d k x) = index A mu (Syn.subst σ d) (Syn.subst σ k) (Syn.subst σ x) := by simp [index]
@[simp] theorem subst_minimizer {q : ℕ} (σ : Fin n → PTm q) (A : PR 3) (mu : PR 2) (d k x : PTm n) :
    Syn.subst σ (minimizer A mu d k x) = minimizer A mu (Syn.subst σ d) (Syn.subst σ k) (Syn.subst σ x) := by simp [minimizer]
@[simp] theorem subst_minimum {q : ℕ} (σ : Fin n → PTm q) (A : PR 3) (mu : PR 2) (d k x : PTm n) :
    Syn.subst σ (minimum A mu d k x) = minimum A mu (Syn.subst σ d) (Syn.subst σ k) (Syn.subst σ x) := by simp [minimum]

theorem well_formed_congr {q q' : PTm n} (e : Γ ⊢[PRAAx] q ≐ q') (h : Γ ⊢[PRAAx] RationalNormalForm.wellFormed q) :
    Γ ⊢[PRAAx] RationalNormalForm.wellFormed q' := by
  have proof := Prf.eqSubst (RationalNormalForm.wellFormed (var 0) : Fm PTm 1) ![q] ![q']
    (fun i => by fin_cases i; exact e) (by simpa using h)
  simpa using proof

theorem point_presented (d t w : PTm n) : Γ ⊢[PRAAx] presentedCube (point d t w) d := by
  refine .andI (RationalCubeGrid.point_cube _ _ _) (.allI (.impI ?_))
  let Δ := lt (var 0) (Syn.shift d) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (Syn.shift d) := Prf.hyp0
  simpa only [Δ,Syn.shift,RationalCubeGrid.subst_point] using
    well_formed_congr (RationalCubeGrid.point_lookup (Syn.shift d) (Syn.shift t) (Syn.shift w) (var 0) hi).eqSymm
      (RationalCubeGrid.fraction_canonical _ _)

theorem data_fields (d k x : PTm n) : Γ ⊢[PRAAx] fstT (data d k x) ≐ d ⋏
    (fstT (sndT (data d k x)) ≐ k ⋏ sndT (sndT (data d k x)) ≐ x) :=
  .andI (fst_pair _ _) (.andI ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)))
theorem score_body_at (A : PR 3) (mu : PR 2) (d k x i : PTm n) : Γ ⊢[PRAAx]
    inst2 (scoreBody A mu) i (data d k x) ≐ score A mu d k x i := by
  have e := data_fields (Γ := Γ) d k x
  simp only [scoreBody,inst2,subst_score,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  simpa only [subst_score,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (score A mu (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![fstT (data d k x),fstT (sndT (data d k x)),sndT (sndT (data d k x)),i]) (σ' := ![d,k,x,i])
      (fun j => by fin_cases j; exact .andE₁ e; exact .andE₁ (.andE₂ e); exact .andE₂ (.andE₂ e); exact .eqRefl _)
theorem score_program_at (A : PR 3) (mu : PR 2) (d k x i : PTm n) : Γ ⊢[PRAAx]
    ap2 (scoreF A mu) i (data d k x) ≐ score A mu d k x i :=
  (toPR_eq (scoreBody A mu) ![i,data d k x]).eqTrans (score_body_at A mu d k x i)
theorem horizon_positive (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] le one (horizon mu d k x) := RationalCubeGrid.count_positive _ _
theorem index_bound (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] lt (index A mu d k x) (horizon mu d k x) :=
  lt_congr (.eqRefl _) (Foundations.FiniteHausdorff.positive_length (horizon_positive mu d k x)).eqSymm
    ((succ_monus_succ (index A mu d k x) (pred (horizon mu d k x))).eqTrans
      (RationalArgmin.selected_spec (scoreF A mu) (pred (horizon mu d k x)) (data d k x)))
theorem minimizer_presented (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] presentedCube (minimizer A mu d k x) d := point_presented _ _ _
theorem minimum_le_score (A : PR 3) (mu : PR 2) (d k x i : PTm n) (hi : Γ ⊢[PRAAx] lt i (horizon mu d k x)) :
    Γ ⊢[PRAAx] rationalLE (minimum A mu d k x) (score A mu d k x i) := by
  have ip : Γ ⊢[PRAAx] le i (pred (horizon mu d k x)) :=
    (succ_monus_succ i (pred (horizon mu d k x))).eqSymm.eqTrans (lt_congr (.eqRefl _) (Foundations.FiniteHausdorff.positive_length (horizon_positive mu d k x)) hi)
  exact rationalLE_congr (score_program_at A mu d k x (index A mu d k x)) (score_program_at A mu d k x i)
    (RationalArgmin.selected_minimal _ _ _ _ ip)

def coherentAt (A : PR 3) (y p q x : PTm n) : Fm PTm n :=
  RationalValueBounds.radius (sample A y p x) (sample A y q x) (scale p+scale q) (scale p*scale q)
def coherence (A : PR 3) (d x : PTm n) : Fm PTm n := .all
  (presentedCube (var 0) (Syn.shift d) ⟶ .all (.all
    (coherentAt A (var 2) (var 1) (var 0) (Syn.shift (Syn.shift (Syn.shift x))))))
def errorNumerator (l p q : PTm n) : PTm n := scale p*scale q+scale l*(scale p+scale q)
def errorDenominator (l p q : PTm n) : PTm n := scale l*scale p*scale q
def continuousAt (A : PR 3) (mu : PR 2) (d x y z l p q : PTm n) : Fm PTm n :=
  RationalHausdorff.pointRadius y z d one (scale (ap2 mu l x)) ⟶
    RationalValueBounds.radius (sample A y p x) (sample A z q x) (errorNumerator l p q) (errorDenominator l p q)
def continuity (A : PR 3) (mu : PR 2) (d x : PTm n) : Fm PTm n := .all (.all
  (presentedCube (var 1) (Syn.shift (Syn.shift d)) ⟶ presentedCube (var 0) (Syn.shift (Syn.shift d)) ⟶
    .all (.all (.all (continuousAt A mu (Syn.shift (Syn.shift (Syn.shift (Syn.shift (Syn.shift d)))))
      (Syn.shift (Syn.shift (Syn.shift (Syn.shift (Syn.shift x))))) (var 4) (var 3) (var 2) (var 1) (var 0))))))

@[simp] theorem subst_coherentAt {q : ℕ} (σ : Fin n → PTm q) (A : PR 3) (y p l x : PTm n) :
    (coherentAt A y p l x).subst σ = coherentAt A (Syn.subst σ y) (Syn.subst σ p) (Syn.subst σ l) (Syn.subst σ x) := by simp [coherentAt]
@[simp] theorem subst_coherence {q : ℕ} (σ : Fin n → PTm q) (A : PR 3) (d x : PTm n) :
    (coherence A d x).subst σ = coherence A (Syn.subst σ d) (Syn.subst σ x) := by simp [coherence,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_errorNumerator {v : ℕ} (σ : Fin n → PTm v) (l p q : PTm n) :
    Syn.subst σ (errorNumerator l p q) = errorNumerator (Syn.subst σ l) (Syn.subst σ p) (Syn.subst σ q) := by simp [errorNumerator]
@[simp] theorem subst_errorDenominator {v : ℕ} (σ : Fin n → PTm v) (l p q : PTm n) :
    Syn.subst σ (errorDenominator l p q) = errorDenominator (Syn.subst σ l) (Syn.subst σ p) (Syn.subst σ q) := by simp [errorDenominator]
@[simp] theorem subst_continuousAt {v : ℕ} (σ : Fin n → PTm v) (A : PR 3) (mu : PR 2) (d x y z l p q : PTm n) :
    (continuousAt A mu d x y z l p q).subst σ = continuousAt A mu (Syn.subst σ d) (Syn.subst σ x)
      (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ l) (Syn.subst σ p) (Syn.subst σ q) := by simp [continuousAt,one]
@[simp] theorem subst_continuity {v : ℕ} (σ : Fin n → PTm v) (A : PR 3) (mu : PR 2) (d x : PTm n) :
    (continuity A mu d x).subst σ = continuity A mu (Syn.subst σ d) (Syn.subst σ x) := by
  simp [continuity,Syn.subst_shift,Syn.shift_subst]

theorem coherence_at (A : PR 3) (d x y p q : PTm n) (h : Γ ⊢[PRAAx] coherence A d x)
    (hy : Γ ⊢[PRAAx] presentedCube y d) : Γ ⊢[PRAAx] coherentAt A y p q x := by
  have r0 : Γ ⊢[PRAAx] presentedCube y d ⟶ .all (.all
      (coherentAt A (Syn.shift (Syn.shift y)) (var 1) (var 0) (Syn.shift (Syn.shift x)))) := by
    simpa [coherence,Syn.subst_shift,Syn.shift_subst,Syn.shift,Syn.subst_subst,Function.comp_def] using h.allE y
  have r1 : Γ ⊢[PRAAx] .all (coherentAt A (Syn.shift y) (Syn.shift p) (var 0) (Syn.shift x)) := by
    simpa [Syn.subst_shift,Syn.shift_subst,Syn.shift,Syn.subst_subst,Function.comp_def] using (Prf.impE r0 hy).allE p
  simpa using r1.allE q

theorem continuity_at (A : PR 3) (mu : PR 2) (d x y z l p q : PTm n) (h : Γ ⊢[PRAAx] continuity A mu d x)
    (hy : Γ ⊢[PRAAx] presentedCube y d) (hz : Γ ⊢[PRAAx] presentedCube z d)
    (hr : Γ ⊢[PRAAx] RationalHausdorff.pointRadius y z d one (scale (ap2 mu l x))) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (sample A y p x) (sample A z q x) (errorNumerator l p q) (errorDenominator l p q) := by
  have r0 : Γ ⊢[PRAAx] presentedCube y d ⟶ presentedCube z d ⟶ .all (.all (.all
      (continuousAt A mu (Syn.shift (Syn.shift (Syn.shift d))) (Syn.shift (Syn.shift (Syn.shift x)))
        (Syn.shift (Syn.shift (Syn.shift y))) (Syn.shift (Syn.shift (Syn.shift z))) (var 2) (var 1) (var 0)))) := by
    simpa [continuity,Syn.subst_shift,Syn.shift_subst,Syn.shift,Syn.subst_subst,Function.comp_def] using (h.allE y).allE z
  have r1 : Γ ⊢[PRAAx] .all (.all (continuousAt A mu (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x))
      (Syn.shift (Syn.shift y)) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift l)) (var 1) (var 0))) := by
    simpa [Syn.subst_shift,Syn.shift_subst,Syn.shift,Syn.subst_subst,Function.comp_def] using (Prf.impE (Prf.impE r0 hy) hz).allE l
  have r2 : Γ ⊢[PRAAx] .all (continuousAt A mu (Syn.shift d) (Syn.shift x) (Syn.shift y) (Syn.shift z)
      (Syn.shift l) (Syn.shift p) (var 0)) := by simpa [Syn.subst_shift,Syn.shift_subst,Syn.shift,Syn.subst_subst,Function.comp_def] using r1.allE p
  have r3 : Γ ⊢[PRAAx] continuousAt A mu d x y z l p q := by simpa using r2.allE q
  exact .impE r3 hr

theorem error_denominator_positive (l p q : PTm n) : Γ ⊢[PRAAx] le one (errorDenominator l p q) :=
  RationalAlgebra.positive_product (RationalAlgebra.positive_product (RationalCubeGrid.scale_positive l) (RationalCubeGrid.scale_positive p))
    (RationalCubeGrid.scale_positive q)
theorem scale_precision (k : PTm n) : Γ ⊢[PRAAx] scale (precision k) ≐ scale (succ k)*two := pw_succ _ _

theorem minimum_le_rounded (A : PR 3) (mu : PR 2) (d k x y : PTm n) (hy : Γ ⊢[PRAAx] presentedCube y d) :
    Γ ⊢[PRAAx] rationalLE (minimum A mu d k x)
      (sample A (point d (mesh mu k x) (RationalCubeGrid.roundIndex y d (mesh mu k x))) (precision k) x) :=
  minimum_le_score A mu d k x _ (RationalCubeGrid.round_index_bound y d _ (.andE₁ hy))

/-- The original half-error lower enclosure for every presented rational point. -/
theorem minimum_upper (A : PR 3) (mu : PR 2) (d k x y p : PTm n) (h : Γ ⊢[PRAAx] continuity A mu d x)
    (hy : Γ ⊢[PRAAx] presentedCube y d) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (minimum A mu d k x) (sample A y p x)
      (scale (succ k)+scale p) (scale (succ k)*scale p) := by
  let z := point d (mesh mu k x) (RationalCubeGrid.roundIndex y d (mesh mu k x))
  have delta : Γ ⊢[PRAAx] RationalValueBounds.radius (sample A y p x) (sample A z (precision k) x)
      (errorNumerator (precision k) p (precision k)) (errorDenominator (precision k) p (precision k)) :=
    continuity_at A mu d x y z (precision k) p (precision k) h hy (point_presented _ _ _)
      (RationalCubeGrid.rounded_point_radius y d (mesh mu k x) (.andE₁ hy))
  have upper := RationalValueBounds.upper_order_left (minimum A mu d k x) (sample A z (precision k) x) (sample A y p x) _ _
    (minimum_le_rounded A mu d k x y hy)
    (RationalValueBounds.upper_of_radius _ _ _ _ (RationalValueBounds.radius_symmetric _ _ _ _ delta))
  apply RationalValueBounds.upper_mono _ _ _ _ _ _ (error_denominator_positive _ _ _) upper
  apply le_of_eq_add (d := zero)
  unfold errorNumerator errorDenominator
  apply deriveNat
  ipra_simps
  rw [natEq (scale_precision (Γ := Γ) k)]
  ipra_simps
  ring

/-- The actual selected point has the source quarter-error upper enclosure. -/
theorem minimizer_upper (A : PR 3) (mu : PR 2) (d k x p : PTm n) (h : Γ ⊢[PRAAx] coherence A d x) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (sample A (minimizer A mu d k x) p x) (minimum A mu d k x)
      (scale (precision k)+scale p) (scale (precision k)*scale p) :=
  RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _)
    (RationalValueBounds.upper_of_radius _ _ _ _ (coherence_at A d x (minimizer A mu d k x) p (precision k) h
      (minimizer_presented A mu d k x)))

def output (A : PR 3) (mu : PR 2) (d k x : PTm n) : PTm n := pairT (minimizer A mu d k x)
  (pairT (minimum A mu d k x) (pairT (index A mu d k x) (pairT (mesh mu k x) (horizon mu d k x))))
def outputF (A : PR 3) (mu : PR 2) : PR 3 := PTm.toPR (output A mu (var 0) (var 1) (var 2))
def run (A : PR 3) (mu : PR 2) (d k x : PTm n) : PTm n := app (outputF A mu) ![d,k,x]
@[simp] theorem subst_output {q : ℕ} (σ : Fin n → PTm q) (A : PR 3) (mu : PR 2) (d k x : PTm n) :
    Syn.subst σ (output A mu d k x) = output A mu (Syn.subst σ d) (Syn.subst σ k) (Syn.subst σ x) := by simp [output]
@[simp] theorem subst_run {q : ℕ} (σ : Fin n → PTm q) (A : PR 3) (mu : PR 2) (d k x : PTm n) :
    Syn.subst σ (run A mu d k x) = run A mu (Syn.subst σ d) (Syn.subst σ k) (Syn.subst σ x) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] run A mu d k x ≐ output A mu d k x := by
  simpa [run,outputF,Matrix.cons_val_succ',Matrix.cons_val_zero'] using
    toPR_eq (Γ := Γ) (output A mu (var 0) (var 1) (var 2) : PTm 3) ![d,k,x]
theorem returned_minimizer (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] fstT (run A mu d k x) ≐ minimizer A mu d k x :=
  (congrFst (program_at A mu d k x)).eqTrans (fst_pair _ _)
theorem returned_minimum (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run A mu d k x)) ≐ minimum A mu d k x :=
  (congrFst ((congrSnd (program_at A mu d k x)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
private theorem returned_tail (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run A mu d k x)) ≐
    pairT (index A mu d k x) (pairT (mesh mu k x) (horizon mu d k x)) :=
  (congrSnd ((congrSnd (program_at A mu d k x)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_index (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run A mu d k x))) ≐ index A mu d k x :=
  (congrFst (returned_tail A mu d k x)).eqTrans (fst_pair _ _)
theorem returned_mesh (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run A mu d k x)))) ≐ mesh mu k x :=
  (congrFst ((congrSnd (returned_tail A mu d k x)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_horizon (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run A mu d k x)))) ≐ horizon mu d k x :=
  (congrSnd ((congrSnd (returned_tail A mu d k x)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_presented (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] presentedCube (fstT (run A mu d k x)) d := by
  have proof := Prf.eqSubst (Γ := Γ) (presentedCube (var 0) (var 1) : Fm PTm 2)
    ![minimizer A mu d k x,d] ![fstT (run A mu d k x),d]
    (fun i => by fin_cases i; exact (returned_minimizer A mu d k x).eqSymm; exact .eqRefl _)
    (by simpa using minimizer_presented (Γ := Γ) A mu d k x)
  simpa using proof

theorem returned_minimum_upper (A : PR 3) (mu : PR 2) (d k x y p : PTm n) (h : Γ ⊢[PRAAx] continuity A mu d x)
    (hy : Γ ⊢[PRAAx] presentedCube y d) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (fstT (sndT (run A mu d k x))) (sample A y p x)
      (scale (succ k)+scale p) (scale (succ k)*scale p) :=
  RationalValueBounds.upper_congr (returned_minimum A mu d k x).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (minimum_upper A mu d k x y p h hy)
theorem returned_minimizer_upper (A : PR 3) (mu : PR 2) (d k x p : PTm n) (h : Γ ⊢[PRAAx] coherence A d x) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (sample A (fstT (run A mu d k x)) p x) (fstT (sndT (run A mu d k x)))
      (scale (precision k)+scale p) (scale (precision k)*scale p) :=
  RationalValueBounds.upper_congr (congrAp3 A (returned_minimizer A mu d k x).eqSymm (.eqRefl _) (.eqRefl _))
    (returned_minimum A mu d k x).eqSymm (.eqRefl _) (.eqRefl _) (minimizer_upper A mu d k x p h)

theorem actual_cube_minimum_index_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (index A mu (var 0) (var 1) (var 2)) (horizon mu (var 0) (var 1) (var 2))) := closeUniv 3 (index_bound _ _ _ _ _)
theorem actual_cube_minimizer_presented_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (presentedCube (minimizer A mu (var 0) (var 1) (var 2)) (var 0)) := closeUniv 3 (minimizer_presented _ _ _ _ _)
theorem actual_cube_sampled_minimum_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (horizon mu (var 0) (var 1) (var 2)) ⟶
      rationalLE (minimum A mu (var 0) (var 1) (var 2)) (score A mu (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (minimum_le_score _ _ _ _ _ _ Prf.hyp0))
theorem actual_original_sampler_coherence_closed (A : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (coherence A (var 0) (var 1) ⟶ presentedCube (var 2) (var 0) ⟶ coherentAt A (var 2) (var 3) (var 4) (var 1)) :=
  closeUniv 5 (.impI (.impI (coherence_at _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_original_uniform_continuity_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (continuity A mu (var 0) (var 1) ⟶ presentedCube (var 2) (var 0) ⟶ presentedCube (var 3) (var 0) ⟶
      RationalHausdorff.pointRadius (var 2) (var 3) (var 0) one (scale (ap2 mu (var 4) (var 1))) ⟶
        RationalValueBounds.radius (sample A (var 2) (var 5) (var 1)) (sample A (var 3) (var 6) (var 1))
          (errorNumerator (var 4) (var 5) (var 6)) (errorDenominator (var 4) (var 5) (var 6))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (continuity_at _ _ _ _ _ _ _ _ _ (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0)))))
theorem actual_cube_minimum_half_budget_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (continuity A mu (var 0) (var 2) ⟶ presentedCube (var 3) (var 0) ⟶
      RationalValueBounds.upper (minimum A mu (var 0) (var 1) (var 2)) (sample A (var 3) (var 4) (var 2))
        (scale (succ (var 1))+scale (var 4)) (scale (succ (var 1))*scale (var 4))) :=
  closeUniv 5 (.impI (.impI (minimum_upper _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_cube_minimizer_quarter_budget_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (coherence A (var 0) (var 2) ⟶ RationalValueBounds.upper
      (sample A (minimizer A mu (var 0) (var 1) (var 2)) (var 3) (var 2)) (minimum A mu (var 0) (var 1) (var 2))
      (scale (precision (var 1))+scale (var 3)) (scale (precision (var 1))*scale (var 3))) :=
  closeUniv 4 (.impI (minimizer_upper _ _ _ _ _ _ Prf.hyp0))
theorem actual_cube_minimum_program_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run A mu (var 0) (var 1) (var 2) ≐ output A mu (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _ _ _)
theorem actual_returned_cube_minimizer_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (presentedCube (fstT (run A mu (var 0) (var 1) (var 2))) (var 0)) := closeUniv 3 (returned_presented _ _ _ _ _)
theorem actual_returned_cube_minimum_budget_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (continuity A mu (var 0) (var 2) ⟶ presentedCube (var 3) (var 0) ⟶
      RationalValueBounds.upper (fstT (sndT (run A mu (var 0) (var 1) (var 2)))) (sample A (var 3) (var 4) (var 2))
        (scale (succ (var 1))+scale (var 4)) (scale (succ (var 1))*scale (var 4))) :=
  closeUniv 5 (.impI (.impI (returned_minimum_upper _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalCubeMinimum
