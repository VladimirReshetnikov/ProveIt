import IPRADerivations.Analysis.GaussianNamedFiniteProduct
import IPRADerivations.Analysis.GaussianRationalNormSquareTransport

/-!
# Multiplicative transformations of the actual finite observation product

Maps preserving one and multiplication commute with the literal
precision-first finite row loop. This includes both Gaussian norm
square and the ordinary algebraic square.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNamedFiniteProductMap

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedFiniteProduct (sample sample_zero sample_succ)
open GaussianRationalHorner (qmul)
open GaussianRationalNormSquareTransport (value value_congr product_value)
open GaussianRationalConjugation (point_one)
open GaussianRationalReciprocal (qone)
open GaussianReciprocalHorner (qmul_one_right)
open GaussianRationalSyntheticDivision (qmul_congr qone_canonical)
open GaussianRationalPowerAlgebra (qmul_shuffle)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def applyMap (h : PTm 1) (a : PTm n) : PTm n := Syn.subst ![a] h
def mapBody (h : PTm 1) (f : PR 3) : PTm 3 := applyMap h (ap3 f (var 0) (var 1) (var 2))
def mapF (h : PTm 1) (f : PR 3) : PR 3 := PTm.toPR (mapBody h f)

@[simp] theorem subst_applyMap {L : ℕ} (σ : Fin n → PTm L) (h : PTm 1) (a : PTm n) :
    Syn.subst σ (applyMap h a) = applyMap h (Syn.subst σ a) := by
  unfold applyMap
  rw [Syn.subst_subst]
  congr 1
  funext j
  fin_cases j
  rfl

theorem apply_map_congr (h : PTm 1) {a b : PTm n} (e : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] applyMap h a ≐ applyMap h b :=
  Prf.eqCongr h (σ := ![a]) (σ' := ![b]) (fun i => by fin_cases i; exact e)

theorem map_at (h : PTm 1) (f : PR 3) (p i x : PTm n) :
    Γ ⊢[PRAAx] ap3 (mapF h f) p i x ≐ applyMap h (ap3 f p i x) := by
  have args : (fun j : Fin 3 => Syn.subst (![p,i,x] : Fin 3 → PTm n) ((![var 0,var 1,var 2] : Fin 3 → PTm 3) j)) =
      ![p,i,x] := by
    funext j
    fin_cases j <;> rfl
  simpa only [mapF,mapBody,ap3,subst_applyMap,ConciseIPRA.PTm.subst_app,args] using
    toPR_eq (Γ := Γ) (mapBody h f) ![p,i,x]

def law (h : PTm 1) (f : PR 3) (p i x : PTm n) : Fm PTm n :=
  applyMap h (sample f p i x) ≐ sample (mapF h f) p i x

@[simp] theorem subst_law {L : ℕ} (σ : Fin n → PTm L) (h : PTm 1) (f : PR 3) (p i x : PTm n) :
    (law h f p i x).subst σ = law h f (Syn.subst σ p) (Syn.subst σ i) (Syn.subst σ x) := by simp [law]

theorem sample_map (h : PTm 1) (f : PR 3) (p i x : PTm n)
    (hOne : ∀ {l : ℕ} {Δ : List (Fm PTm l)}, Δ ⊢[PRAAx] applyMap h qone ≐ qone)
    (hmul : ∀ {l : ℕ} {Δ : List (Fm PTm l)} (a b : PTm l),
      Δ ⊢[PRAAx] applyMap h (qmul a b) ≐ qmul (applyMap h a) (applyMap h b)) :
    Γ ⊢[PRAAx] law h f p i x := by
  have all : Γ ⊢[PRAAx] .all (law h f (Syn.shift p) (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_law,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (apply_map_congr h (sample_zero f p x)).eqTrans (hOne.eqTrans (sample_zero _ _ _).eqSymm)
    · simp only [subst_law,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      let P := Syn.shift p
      let X := Syn.shift x
      let j : PTm (n+1) := var 0
      let Δ := law h f P j X :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] law h f P j X := Prf.hyp0
      exact (apply_map_congr h (sample_succ f P j X)).eqTrans ((hmul _ _).eqTrans
        ((qmul_congr ih (map_at h f P j X).eqSymm).eqTrans (sample_succ _ _ _ _).eqSymm))
  simpa only [subst_law,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE i

def normF (f : PR 3) : PR 3 := mapF (value (var 0)) f
def squareF (f : PR 3) : PR 3 := mapF (qmul (var 0) (var 0)) f

theorem norm_at (f : PR 3) (p i x : PTm n) :
    Γ ⊢[PRAAx] ap3 (normF f) p i x ≐ value (ap3 f p i x) := by
  simpa [normF,applyMap] using map_at (value (var 0)) f p i x

theorem square_at (f : PR 3) (p i x : PTm n) :
    Γ ⊢[PRAAx] ap3 (squareF f) p i x ≐ qmul (ap3 f p i x) (ap3 f p i x) := by
  simpa [squareF,applyMap] using map_at (qmul (var 0) (var 0)) f p i x

theorem sample_norm (f : PR 3) (p i x : PTm n) :
    Γ ⊢[PRAAx] value (sample f p i x) ≐ sample (normF f) p i x := by
  have one : ∀ {l : ℕ} {Δ : List (Fm PTm l)}, Δ ⊢[PRAAx] applyMap (value (var 0)) qone ≐ qone := by
    intro l Δ
    unfold applyMap
    simp only [GaussianRationalNormSquareTransport.subst_value,Syn.subst_var,Matrix.cons_val_zero]
    exact (qmul_congr (.eqRefl _) point_one).eqTrans (qmul_one_right _ qone_canonical)
  have mul : ∀ {l : ℕ} {Δ : List (Fm PTm l)} (a b : PTm l),
      Δ ⊢[PRAAx] applyMap (value (var 0)) (qmul a b) ≐
        qmul (applyMap (value (var 0)) a) (applyMap (value (var 0)) b) := by
    intro l Δ a b
    simpa [applyMap] using (product_value (Γ := Δ) a b)
  simpa [law,normF,applyMap] using sample_map (value (var 0)) f p i x one mul

theorem sample_square (f : PR 3) (p i x : PTm n) :
    Γ ⊢[PRAAx] qmul (sample f p i x) (sample f p i x) ≐ sample (squareF f) p i x := by
  let T : PTm 1 := qmul (var 0) (var 0)
  have one : ∀ {l : ℕ} {Δ : List (Fm PTm l)}, Δ ⊢[PRAAx] applyMap T qone ≐ qone := by
    intro l Δ
    simp only [T,applyMap,GaussianRationalHorner.subst_qmul,Syn.subst_var,Matrix.cons_val_zero]
    exact qmul_one_right qone qone_canonical
  have mul : ∀ {l : ℕ} {Δ : List (Fm PTm l)} (a b : PTm l),
      Δ ⊢[PRAAx] applyMap T (qmul a b) ≐ qmul (applyMap T a) (applyMap T b) := by
    intro l Δ a b
    simpa [T,applyMap] using (qmul_shuffle (Γ := Δ) a b a b)
  simpa [law,squareF,T,applyMap] using sample_map T f p i x one mul

end LeanProofs.IPRA.Analysis.GaussianNamedFiniteProductMap
