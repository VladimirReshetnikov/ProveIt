import IPRADerivations.Core.Order
import IPRADerivations.Core.InductionTactic

/-!
# Pairing and simultaneous recursion in iPRA

* `eqb a b = 1 ∸ ((a ∸ b) + (b ∸ a))`, the characteristic term of equality, with
  `eqb_of_eq` and `eqb_of_ne`.
* The integer square root `isqrt`, defined by
  `isqrt 0 = 0`, `isqrt (z + 1) = isqrt z + eqb ((isqrt z + 1)², z + 1)`, with the
  invariant `isqrt z ² ≤ z < (isqrt z + 1)²` (`isqrt_spec`) and uniqueness
  (`isqrt_unique`).
* The pairing `⟨a, b⟩ = (a + b)² + a`, with projections `fst z = z ∸ (isqrt z)²` and
  `snd z = isqrt z ∸ fst z`, and `fst ⟨a, b⟩ = a`, `snd ⟨a, b⟩ = b`.
* Simultaneous primitive recursion of two sequences (`sim₁`, `sim₂`): from base
  terms `b₁, b₂` and step terms `s₁, s₂`, the equations
  `simᵢ(0, x⃗) = bᵢ(x⃗)` and `simᵢ(y + 1, x⃗) = sᵢ(y, sim₁(y, x⃗), sim₂(y, x⃗), x⃗)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open PTm (pred monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The numeral `1`. -/
abbrev one : PTm n := succ zero

/-! ## The equality test -/

/-- `eqb a b = 1` if `a = b` and `0` otherwise. -/
def eqb (a b : PTm n) : PTm n := monus one (monus a b + monus b a)

ipra_subst eqb

theorem eqb_of_eq {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] eqb a b ≐ one := by
  unfold eqb
  refine (congrMonus (.eqRefl _) ?_).eqTrans (monus_zero _)
  refine (congrAdd (congrMonus h (.eqRefl b)) (congrMonus h.eqSymm (.eqRefl a))).eqTrans ?_
  exact (congrAdd (monus_self b) (monus_self a)).eqTrans (add_zero _)

theorem add_eq_zero_left {x y : PTm n} (h : Γ ⊢[PRAAx] x + y ≐ zero) : Γ ⊢[PRAAx] x ≐ zero := by
  refine .orE (zero_or_succ x) Prf.hyp0 ?_
  exact succ_ne_zero' _ ((succ_add _ _).eqSymm.eqTrans
    ((congrAdd Prf.hyp0 (.eqRefl y)).eqSymm.eqTrans h.wk))

theorem eqb_of_ne {a b : PTm n} (h : Γ ⊢[PRAAx] neg (a ≐ b)) : Γ ⊢[PRAAx] eqb a b ≐ zero := by
  unfold eqb
  refine .orE (zero_or_succ (monus a b + monus b a)) ?_ ?_
  · refine .botE _ (.impE h.wk (le_antisymm ?_ ?_))
    · exact add_eq_zero_left Prf.hyp0
    · exact add_eq_zero_left ((add_comm _ _).eqTrans Prf.hyp0)
  · exact (congrMonus (.eqRefl _) Prf.hyp0).eqTrans
      ((succ_monus_succ _ _).eqTrans (zero_monus _))

/-! ## The integer square root -/

/-- The step term of `isqrt`: variables `0 = z`, `1 = isqrt z`. -/
abbrev isqrtStep : PTm 2 := var 1 + eqb ((var 1 + one) * (var 1 + one)) (succ (var 0))

/-- `isqrt`. -/
abbrev isqrtF : PR 1 := rec1 zero isqrtStep

/-- `isqrt z`. -/
abbrev isqrt (z : PTm n) : PTm n := ap1 isqrtF z

theorem isqrt_zero : Γ ⊢[PRAAx] isqrt (zero : PTm n) ≐ zero := by
  simpa using rec1_zero (Γ := Γ) zero isqrtStep

theorem isqrt_succ (z : PTm n) :
    Γ ⊢[PRAAx] isqrt (succ z) ≐ isqrt z + eqb ((isqrt z + one) * (isqrt z + one)) (succ z) := by
  have h := rec1_succ (Γ := Γ) zero isqrtStep z
  simpa using h

/-- The invariant `(isqrt z)² ≤ z < (isqrt z + 1)²`. -/
abbrev isqrtInv : Fm PTm 1 :=
  le (isqrt (var 0) * isqrt (var 0)) (var 0) ⋏
    lt (var 0) ((isqrt (var 0) + one) * (isqrt (var 0) + one))

private theorem isqrt_spec₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] isqrtInv := by
  ipra_ind (⟨le_QF _ _, lt_QF _ _⟩) [subst_le, subst_lt, subst_ap1]
  · have e := isqrt_zero (Γ := ([] : List (Fm PTm 0)))
    refine .andI ?_ ?_
    · exact le_congr (((congrMul e e).eqTrans (mul_zero _)).eqSymm) (.eqRefl _) (le_refl _)
    · refine le_congr (.eqRefl _) ?_ (le_refl one)
      exact (deriveNat (by have e' := natEq e; ipra_simps; rw [e']; ring)).eqSymm
  · -- Context [isqrtInv]; r = isqrt v, r' = isqrt (S v).
    have hI₁ : [isqrtInv] ⊢[PRAAx] le (isqrt (var 0) * isqrt (var 0)) (var 0) := .andE₁ Prf.hyp0
    have hI₂ : [isqrtInv] ⊢[PRAAx] lt (var 0) ((isqrt (var 0) + one) * (isqrt (var 0) + one)) :=
      .andE₂ Prf.hyp0
    have hs := isqrt_succ (Γ := [isqrtInv]) (var 0)
    refine .orE (eq_or_ne ((isqrt (var 0) + one) * (isqrt (var 0) + one)) (succ (var 0))) ?_ ?_
    · -- (r + 1)² = S v, so r' = r + 1.
      have hE : ((_ : Fm PTm 1) :: [isqrtInv]) ⊢[PRAAx] (isqrt (var 0) + one) * (isqrt (var 0) + one) ≐ succ (var 0) := Prf.hyp0
      have hr : ((_ : Fm PTm 1) :: [isqrtInv]) ⊢[PRAAx] isqrt (succ (var 0)) ≐ isqrt (var 0) + one :=
        hs.wk.eqTrans (congrAdd (.eqRefl _) (eqb_of_eq hE))
      refine .andI ?_ ?_
      · exact le_congr ((congrMul hr hr).eqTrans hE).eqSymm (.eqRefl _) (le_refl _)
      · refine le_of_eq_add (d := succ (succ zero) * isqrt (var 0) + succ (succ zero)) ?_
        apply deriveNat
        have e₁ := natEq hr
        have e₂ := natEq hE
        ipra_simps
        rw [e₁]
        linear_combination e₂
    · -- (r + 1)² ≠ S v, so r' = r.
      have hN : ((_ : Fm PTm 1) :: [isqrtInv]) ⊢[PRAAx] neg ((isqrt (var 0) + one) * (isqrt (var 0) + one) ≐ succ (var 0)) :=
        Prf.hyp0
      have hr : ((_ : Fm PTm 1) :: [isqrtInv]) ⊢[PRAAx] isqrt (succ (var 0)) ≐ isqrt (var 0) :=
        hs.wk.eqTrans ((congrAdd (.eqRefl _) (eqb_of_ne hN)).eqTrans (add_zero _))
      refine .andI ?_ ?_
      · exact le_congr (congrMul hr hr).eqSymm (.eqRefl _) (le_trans hI₁.wk (le_succ_self _))
      · refine .orE (lt_or_eq_of_le hI₂.wk) ?_ ?_
        · exact lt_congr (.eqRefl _)
            (congrMul (congrAdd hr.wk.eqSymm (.eqRefl _)) (congrAdd hr.wk.eqSymm (.eqRefl _))) Prf.hyp0
        · exact .botE _ (.impE hN.wk Prf.hyp0.eqSymm)

theorem isqrt_le (z : PTm n) : Γ ⊢[PRAAx] le (isqrt z * isqrt z) z := by
  have h := inst (Γ := Γ) isqrt_spec₀ ![z]
  simp at h
  exact .andE₁ h

theorem lt_isqrt_succ_sq (z : PTm n) : Γ ⊢[PRAAx] lt z ((isqrt z + one) * (isqrt z + one)) := by
  have h := inst (Γ := Γ) isqrt_spec₀ ![z]
  simp at h
  exact .andE₂ h

theorem sq_le_sq {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] le (a * a) (b * b) :=
  le_trans (mul_le_mul_right a h) (le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right b h))

/-- If `t² ≤ z < (t + 1)²` then `isqrt z = t`. -/
theorem isqrt_unique {t z : PTm n} (h₁ : Γ ⊢[PRAAx] le (t * t) z)
    (h₂ : Γ ⊢[PRAAx] lt z ((t + one) * (t + one))) : Γ ⊢[PRAAx] isqrt z ≐ t := by
  have hS : ∀ {Δ : List (Fm PTm n)} (u : PTm n), Δ ⊢[PRAAx] succ u ≐ u + one :=
    fun u => succ_eq_add_one u
  refine .orE (lt_or_le (isqrt z) t) ?_ ?_
  · -- isqrt z < t: (isqrt z + 1)² ≤ t² ≤ z < (isqrt z + 1)².
    have hsq := sq_le_sq (Γ := _ :: Γ) (Prf.hyp0 : _ ⊢[PRAAx] lt (isqrt z) t)
    have hle : _ ⊢[PRAAx] le ((isqrt z + one) * (isqrt z + one)) z :=
      le_trans (le_congr (congrMul (hS _) (hS _)) (.eqRefl _) hsq) h₁.wk
    exact le_lt_absurd _ hle (lt_isqrt_succ_sq z)
  · refine .orE (lt_or_eq_of_le Prf.hyp0) ?_ (Prf.hyp0.eqSymm)
    have hsq := sq_le_sq (Γ := lt t (isqrt z) :: le t (isqrt z) :: Γ) Prf.hyp0
    have hle : (lt t (isqrt z) :: le t (isqrt z) :: Γ) ⊢[PRAAx] le ((t + one) * (t + one)) z :=
      le_trans (le_congr (congrMul (hS _) (hS _)) (.eqRefl _) hsq) (isqrt_le z)
    exact le_lt_absurd _ hle h₂.wk.wk

/-! ## Pairing -/

/-- `⟨a, b⟩ = (a + b)² + a`. -/
def pairT (a b : PTm n) : PTm n := (a + b) * (a + b) + a
/-- The first projection. -/
def fstT (z : PTm n) : PTm n := monus z (isqrt z * isqrt z)
/-- The second projection. -/
def sndT (z : PTm n) : PTm n := monus (isqrt z) (fstT z)

ipra_subst pairT
ipra_subst fstT
ipra_subst sndT

/-- The quadratic pairing code is monotone in both entries. -/
theorem pairT_mono {a b A B : PTm n} (ha : Γ ⊢[PRAAx] le a A) (hb : Γ ⊢[PRAAx] le b B) :
    Γ ⊢[PRAAx] le (pairT a b) (pairT A B) := by
  have sum := le_trans (add_le_add_right b ha) (add_le_add_left A hb)
  exact le_trans (add_le_add_right a (sq_le_sq sum)) (add_le_add_left ((A + B) * (A + B)) ha)

theorem isqrt_pair (a b : PTm n) : Γ ⊢[PRAAx] isqrt (pairT a b) ≐ a + b := by
  refine isqrt_unique (le_add_right _ _) ?_
  refine le_of_eq_add (d := a + succ (succ zero) * b) ?_
  unfold pairT
  ipra_ring

theorem fst_pair (a b : PTm n) : Γ ⊢[PRAAx] fstT (pairT a b) ≐ a := by
  unfold fstT
  have e := isqrt_pair (Γ := Γ) a b
  refine (congrMonus (.eqRefl _) (congrMul e e)).eqTrans ?_
  exact add_monus' a _

theorem snd_pair (a b : PTm n) : Γ ⊢[PRAAx] sndT (pairT a b) ≐ b := by
  unfold sndT
  exact (congrMonus (isqrt_pair a b) (fst_pair a b)).eqTrans (add_monus' b a)

/-- Read a term of three variables after packing the last two arguments into a pair. -/
theorem toPR_pair_eq (body : PTm 3) (p x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (PTm.toPR (Syn.subst ![var 0, fstT (var 1), sndT (var 1)] body)) p (pairT x y) ≐
      Syn.subst ![p, x, y] body := by
  refine (toPR_eq _ ![p, pairT x y]).eqTrans ?_
  simp only [Syn.subst_subst, subst_vecCons, subst_vecEmpty, subst_fstT, subst_sndT,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact Prf.eqCongr body (fun i => by
    fin_cases i
    · exact .eqRefl _
    · exact fst_pair _ _
    · exact snd_pair _ _)

theorem congrFst {z z' : PTm n} (h : Γ ⊢[PRAAx] z ≐ z') : Γ ⊢[PRAAx] fstT z ≐ fstT z' := by
  unfold fstT
  have e := congrAp1 isqrtF h
  exact congrMonus h (congrMul e e)

theorem congrSnd {z z' : PTm n} (h : Γ ⊢[PRAAx] z ≐ z') : Γ ⊢[PRAAx] sndT z ≐ sndT z' := by
  unfold sndT
  exact congrMonus (congrAp1 isqrtF h) (congrFst h)

/-- The first component of a term that equals a pair: `h.fstE`. -/
theorem _root_.LeanProofs.ConciseIPRA.Prf.fstE {z a b : PTm n} (h : Γ ⊢[PRAAx] z ≐ pairT a b) :
    Γ ⊢[PRAAx] fstT z ≐ a := (congrFst h).eqTrans (fst_pair a b)

/-- The second component of a term that equals a pair: `h.sndE`. -/
theorem _root_.LeanProofs.ConciseIPRA.Prf.sndE {z a b : PTm n} (h : Γ ⊢[PRAAx] z ≐ pairT a b) :
    Γ ⊢[PRAAx] sndT z ≐ b := (congrSnd h).eqTrans (snd_pair a b)

/-- Store a nonempty vector as right-nested pairs, with its last entry unpaired. -/
def pairVector : (k : ℕ) → (Fin (k + 1) → PTm n) → PTm n
  | 0, entries => entries 0
  | k + 1, entries => pairT (entries 0) (pairVector k (fun i => entries i.succ))

/-- Read the projections of a right-nested pair vector. -/
def pairVectorField : (k : ℕ) → PTm n → Fin (k + 1) → PTm n
  | 0, z => ![z]
  | k + 1, z => Matrix.vecCons (fstT z) (pairVectorField k (sndT z))

/-- Substituting through a projection is the same as projecting the substituted tuple. -/
theorem subst_pairVectorField {m : ℕ} (σ : Fin n → PTm m) (k : ℕ) (p : PTm n)
    (i : Fin (k + 1)) :
    Syn.subst σ (pairVectorField k p i) = pairVectorField k (Syn.subst σ p) i := by
  induction k generalizing p with
  | zero =>
    rw [Fin.eq_zero i]
    rfl
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact subst_fstT σ p
    · change Syn.subst σ (pairVectorField k (sndT p) j) =
        pairVectorField k (sndT (Syn.subst σ p)) j
      rw [ih, subst_sndT]

theorem pairVectorField_eq (k : ℕ) (entries : Fin (k + 1) → PTm n) {z : PTm n}
    (h : Γ ⊢[PRAAx] z ≐ pairVector k entries) (i : Fin (k + 1)) :
    Γ ⊢[PRAAx] pairVectorField k z i ≐ entries i := by
  induction k generalizing z with
  | zero =>
    rw [Fin.eq_zero i]
    exact h
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h.fstE
    · exact ih (fun j => entries j.succ) h.sndE j

/-- Substituting a packed argument reads back the components in their original order. -/
theorem subst_pairVector_eq {k : ℕ} (body : PTm (k + 2)) (p : PTm n)
    (entries : Fin (k + 1) → PTm n) :
    Γ ⊢[PRAAx] Syn.subst ![p, pairVector k entries]
        (Syn.subst (Matrix.vecCons (var 0) (pairVectorField k (var 1))) body) ≐
      Syn.subst (Matrix.vecCons p entries) body := by
  rw [Syn.subst_subst]
  exact Prf.eqCongr body fun i => by
    refine Fin.cases (.eqRefl _) (fun j => ?_) i
    simp only [Matrix.cons_val_succ, subst_pairVectorField, Syn.subst_var, Matrix.cons_val_one]
    exact pairVectorField_eq k entries (.eqRefl _) j

/-! ## Simultaneous recursion -/

section Simultaneous

variable {k : ℕ}

/-- Reading the step variables `y, u, v, x⃗` from `y, ⟨u, v⟩, x⃗`. -/
def simρ : Fin (k + 3) → PTm (k + 2) :=
  Fin.cases (var 0) (Fin.cases (fstT (var 1)) (Fin.cases (sndT (var 1)) fun j => var j.succ.succ))

/-- The symbol computing `⟨sim₁(y, x⃗), sim₂(y, x⃗)⟩`. -/
def simF (b₁ b₂ : PTm k) (s₁ s₂ : PTm (k + 3)) : PR (k + 1) :=
  recDef (pairT b₁ b₂) (pairT (Syn.subst simρ s₁) (Syn.subst simρ s₂))

/-- The two simultaneously defined sequences. -/
def sim₁ (b₁ b₂ : PTm k) (s₁ s₂ : PTm (k + 3)) (y : PTm n) (xs : Fin k → PTm n) : PTm n :=
  fstT (app (simF b₁ b₂ s₁ s₂) (Fin.cases y xs))
def sim₂ (b₁ b₂ : PTm k) (s₁ s₂ : PTm (k + 3)) (y : PTm n) (xs : Fin k → PTm n) : PTm n :=
  sndT (app (simF b₁ b₂ s₁ s₂) (Fin.cases y xs))

@[simp] theorem subst_sim₁ {m : ℕ} (σ : Fin n → PTm m) (b₁ b₂ : PTm k) (s₁ s₂ : PTm (k + 3))
    (y : PTm n) (xs : Fin k → PTm n) :
    Syn.subst σ (sim₁ b₁ b₂ s₁ s₂ y xs) = sim₁ b₁ b₂ s₁ s₂ (Syn.subst σ y) fun i => Syn.subst σ (xs i) := by
  simp only [sim₁, subst_fstT, PTm.subst_app]
  congr 2; funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

@[simp] theorem subst_sim₂ {m : ℕ} (σ : Fin n → PTm m) (b₁ b₂ : PTm k) (s₁ s₂ : PTm (k + 3))
    (y : PTm n) (xs : Fin k → PTm n) :
    Syn.subst σ (sim₂ b₁ b₂ s₁ s₂ y xs) = sim₂ b₁ b₂ s₁ s₂ (Syn.subst σ y) fun i => Syn.subst σ (xs i) := by
  simp only [sim₂, subst_sndT, PTm.subst_app]
  congr 2; funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

variable (b₁ b₂ : PTm k) (s₁ s₂ : PTm (k + 3)) (xs : Fin k → PTm n)

theorem sim₁_zero : Γ ⊢[PRAAx] sim₁ b₁ b₂ s₁ s₂ zero xs ≐ Syn.subst xs b₁ := by
  unfold sim₁
  refine (congrFst (rec_zero _ _ xs)).eqTrans ?_
  rw [subst_pairT]; exact fst_pair _ _

theorem sim₂_zero : Γ ⊢[PRAAx] sim₂ b₁ b₂ s₁ s₂ zero xs ≐ Syn.subst xs b₂ := by
  unfold sim₂
  refine (congrSnd (rec_zero _ _ xs)).eqTrans ?_
  rw [subst_pairT]; exact snd_pair _ _

private theorem simρ_comp (y A : PTm n) :
    (fun i => Syn.subst (Fin.cases y (Fin.cases A xs) : Fin (k + 2) → PTm n) (simρ i))
      = Fin.cases y (Fin.cases (fstT A) (Fin.cases (sndT A) xs)) := by
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i) i <;>
    simp only [simρ, Fin.cases_succ, Fin.cases_zero, subst_fstT, subst_sndT, Syn.subst_var]
  all_goals rfl

theorem sim₁_succ (y : PTm n) :
    Γ ⊢[PRAAx] sim₁ b₁ b₂ s₁ s₂ (succ y) xs
      ≐ Syn.subst (Fin.cases y (Fin.cases (sim₁ b₁ b₂ s₁ s₂ y xs)
          (Fin.cases (sim₂ b₁ b₂ s₁ s₂ y xs) xs))) s₁ := by
  unfold sim₁
  refine (congrFst (rec_succ _ _ y xs)).eqTrans ?_
  rw [subst_pairT, Syn.subst_subst, simρ_comp]
  exact fst_pair _ _

theorem sim₂_succ (y : PTm n) :
    Γ ⊢[PRAAx] sim₂ b₁ b₂ s₁ s₂ (succ y) xs
      ≐ Syn.subst (Fin.cases y (Fin.cases (sim₁ b₁ b₂ s₁ s₂ y xs)
          (Fin.cases (sim₂ b₁ b₂ s₁ s₂ y xs) xs))) s₂ := by
  unfold sim₂
  refine (congrSnd (rec_succ _ _ y xs)).eqTrans ?_
  rw [subst_pairT, Syn.subst_subst, Syn.subst_subst, simρ_comp]
  exact snd_pair _ _

end Simultaneous

end LeanProofs.IPRA
