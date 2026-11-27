import IPRADerivations.Core.Evaluation
import IPRADerivations.Core.Parity
import IPRADerivations.Core.Signum
import Mathlib.Algebra.BigOperators.Fin
import IPRADerivations.Core.Header

/-!
# Finite sums and products of terms indexed in the metatheory

A reusable piece of the embedding framework: sums and products whose index set is fixed in Lean
(a list, `Fin k`, or any finite type such as the permutations of `Fin d`), as iPRA terms. Motivated by
the cubical Sperner lemma `thm:sperner` of `topology/dimension_invariance_ipra` in every dimension,
where the Kuhn simplices of a cube are indexed by the `d!` permutations.

* `lsum`, `lprod` over a list, `fsum`, `fprod` over `Fin k`, `ftsum` over a finite type (through a
  fixed enumeration of `Finset.univ`); substitution commutes with all of them (`subst_lsum`, …).
* `mk_lsum`, `mk_fsum`, `mk_fprod`, `mk_ftsum`: their images in the quotient semiring `Q Γ` of terms
  modulo provable equality are the Lean sums and products. Rearrangements of a finite sum (fibres,
  bijections, involutions) are therefore Mathlib lemmas about `Finset.sum` in `Q Γ`, and come back to
  iPRA through `Q.exact`.
* `ev_add`, `ev_mul`, `ev_monus`, `ev_succ`, `ev_zero`, `ev_num`, `ev_eqb`, `ev_sg`, `ev_fsum`,
  `ev_fprod`, `ev_subst`: the standard values, for the bounded decision procedure of
  `Foundations/BoundedDecision`.
-/


set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.TermSums

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm BigOperators
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ}

/-! ## Sums and products -/

/-- The sum of a list of terms. -/
def lsum : List (PTm n) → PTm n
  | [] => zero
  | t :: l => t + lsum l

/-- The product of a list of terms. -/
def lprod : List (PTm n) → PTm n
  | [] => one
  | t :: l => t * lprod l

/-- `∑_{i < k} f(i)` for an index fixed in the metatheory. -/
def fsum (k : ℕ) (f : Fin k → PTm n) : PTm n := lsum (List.ofFn f)

/-- `∏_{i < k} f(i)` for an index fixed in the metatheory. -/
def fprod (k : ℕ) (f : Fin k → PTm n) : PTm n := lprod (List.ofFn f)

/-- The sum over a finite type, through a fixed enumeration of its elements. -/
noncomputable def ftsum {ι : Type} [Fintype ι] (f : ι → PTm n) : PTm n :=
  lsum ((Finset.univ : Finset ι).toList.map f)

@[simp] theorem subst_lsum {m : ℕ} (σ : Fin n → PTm m) :
    ∀ l : List (PTm n), Syn.subst σ (lsum l) = lsum (l.map (Syn.subst σ))
  | [] => by simp [lsum]
  | t :: l => by simp [lsum, subst_lsum σ l]

@[simp] theorem subst_lprod {m : ℕ} (σ : Fin n → PTm m) :
    ∀ l : List (PTm n), Syn.subst σ (lprod l) = lprod (l.map (Syn.subst σ))
  | [] => by simp [lprod]
  | t :: l => by simp [lprod, subst_lprod σ l]

@[simp] theorem subst_fsum {m : ℕ} (σ : Fin n → PTm m) (k : ℕ) (f : Fin k → PTm n) :
    Syn.subst σ (fsum k f) = fsum k (fun i => Syn.subst σ (f i)) := by
  simp [fsum, List.map_ofFn, Function.comp_def]

@[simp] theorem subst_fprod {m : ℕ} (σ : Fin n → PTm m) (k : ℕ) (f : Fin k → PTm n) :
    Syn.subst σ (fprod k f) = fprod k (fun i => Syn.subst σ (f i)) := by
  simp [fprod, List.map_ofFn, Function.comp_def]

@[simp] theorem subst_ftsum {m : ℕ} {ι : Type} [Fintype ι] (σ : Fin n → PTm m) (f : ι → PTm n) :
    Syn.subst σ (ftsum f) = ftsum (fun i => Syn.subst σ (f i)) := by
  simp [ftsum, List.map_map, Function.comp_def]

/-! ## Images in the quotient semiring -/

variable (Γ : List (Fm PTm n))

theorem mk_lsum : ∀ l : List (PTm n), Q.mk Γ (lsum l) = (l.map (Q.mk Γ)).sum
  | [] => by simp [lsum]
  | t :: l => by simp [lsum, mk_lsum l]

theorem mk_lprod : ∀ l : List (PTm n), Q.mk Γ (lprod l) = (l.map (Q.mk Γ)).prod
  | [] => by simp [lprod]
  | t :: l => by simp [lprod, mk_lprod l]

theorem mk_fsum (k : ℕ) (f : Fin k → PTm n) : Q.mk Γ (fsum k f) = ∑ i, Q.mk Γ (f i) := by
  simp [fsum, mk_lsum, List.map_ofFn, List.sum_ofFn]

theorem mk_fprod (k : ℕ) (f : Fin k → PTm n) : Q.mk Γ (fprod k f) = ∏ i, Q.mk Γ (f i) := by
  simp [fprod, mk_lprod, List.map_ofFn, List.prod_ofFn]

theorem mk_ftsum {ι : Type} [Fintype ι] (f : ι → PTm n) :
    Q.mk Γ (ftsum f) = ∑ i, Q.mk Γ (f i) := by
  simp only [ftsum, mk_lsum, List.map_map]
  exact Finset.sum_map_toList _ _

theorem mk_two : Q.mk Γ (two : PTm n) = 2 := by
  simp only [Q.mk_succ, Q.mk_zero]; norm_num

variable {Γ}

/-- An equation of the quotient semiring is a derivation. -/
theorem of_mk {s t : PTm n} (h : Q.mk Γ s = Q.mk Γ t) : Γ ⊢[PRAAx] s ≐ t := Q.exact h

/-! ## Standard values -/

section Values

variable (ρ : Fin n → ℕ)

theorem ev_app {k : ℕ} (f : PR k) (ts : Fin k → PTm n) :
    PTm.ev ρ (app f ts) = PR.ev f (fun i => PTm.ev ρ (ts i)) := rfl

theorem pr_ev_prec_zero {k : ℕ} (f : PR k) (g : PR (k + 2)) (a : Fin k → ℕ) :
    PR.ev (.prec f g) (Fin.cons 0 a) = PR.ev f a := by
  simp [PR.ev, Fin.tail_cons]

theorem pr_ev_prec_succ {k : ℕ} (f : PR k) (g : PR (k + 2)) (y : ℕ) (a : Fin k → ℕ) :
    PR.ev (.prec f g) (Fin.cons (y + 1) a) =
      PR.ev g (Fin.cons y (Fin.cons (PR.ev (.prec f g) (Fin.cons y a)) a)) := by
  simp [PR.ev, Fin.tail_cons]

theorem pr_ev_add (a b : ℕ) : PR.ev Sym.add (Fin.cons a (Fin.cons b Fin.elim0)) = a + b := by
  induction a with
  | zero => rw [Sym.add, pr_ev_prec_zero]; simp [PR.ev]
  | succ a ih =>
    rw [Sym.add, pr_ev_prec_succ, ← Sym.add, ih]
    simp [PR.ev]; omega

theorem pr_ev_mul (a b : ℕ) : PR.ev Sym.mul (Fin.cons a (Fin.cons b Fin.elim0)) = a * b := by
  induction a with
  | zero => rw [Sym.mul, pr_ev_prec_zero]; simp [PR.ev, Sym.zeroK]
  | succ a ih =>
    rw [Sym.mul, pr_ev_prec_succ, ← Sym.mul, ih]
    simp only [PR.ev]
    have e : (fun j => PR.ev (![PR.proj 1, PR.proj 2] j)
        (Fin.cons a (Fin.cons (a * b) (Fin.cons b Fin.elim0)) : Fin 3 → ℕ)) =
        Fin.cons (a * b) (Fin.cons b Fin.elim0) := by
      funext j; fin_cases j <;> rfl
    rw [e, pr_ev_add]; ring

theorem pr_ev_pred (a : ℕ) : PR.ev Sym.pred (Fin.cons a Fin.elim0) = a - 1 := by
  cases a with
  | zero => rw [Sym.pred, pr_ev_prec_zero]; rfl
  | succ a => rw [Sym.pred, pr_ev_prec_succ]; simp [PR.ev]

theorem pr_ev_rsub (a b : ℕ) : PR.ev Sym.rsub (Fin.cons a (Fin.cons b Fin.elim0)) = b - a := by
  induction a with
  | zero => rw [Sym.rsub, pr_ev_prec_zero]; simp [PR.ev]
  | succ a ih =>
    rw [Sym.rsub, pr_ev_prec_succ, ← Sym.rsub, ih]
    simp only [PR.ev]
    have e : (fun j => PR.ev (![PR.proj 1] j)
        (Fin.cons a (Fin.cons (b - a) (Fin.cons b Fin.elim0)) : Fin 3 → ℕ)) =
        Fin.cons (b - a) Fin.elim0 := by
      funext j; fin_cases j; rfl
    rw [e, pr_ev_pred]; omega

private theorem vec2 (s t : PTm n) :
    (fun i => PTm.ev ρ (![s, t] i)) = Fin.cons (PTm.ev ρ s) (Fin.cons (PTm.ev ρ t) Fin.elim0) := by
  funext i; fin_cases i <;> rfl

@[simp] theorem ev_add (s t : PTm n) : PTm.ev ρ (s + t) = PTm.ev ρ s + PTm.ev ρ t := by
  rw [PTm.add_def, ev_app, vec2, pr_ev_add]

@[simp] theorem ev_mul (s t : PTm n) : PTm.ev ρ (s * t) = PTm.ev ρ s * PTm.ev ρ t := by
  rw [PTm.mul_def, ev_app, vec2, pr_ev_mul]

@[simp] theorem ev_monus (s t : PTm n) : PTm.ev ρ (monus s t) = PTm.ev ρ s - PTm.ev ρ t := by
  show PR.ev Sym.rsub (fun i => PTm.ev ρ (![t, s] i)) = _
  rw [vec2, pr_ev_rsub]

@[simp] theorem ev_zero : PTm.ev ρ (zero : PTm n) = 0 := rfl

@[simp] theorem ev_succ (t : PTm n) : PTm.ev ρ (succ t) = PTm.ev ρ t + 1 := rfl

@[simp] theorem ev_num : ∀ k : ℕ, PTm.ev ρ (num k : PTm n) = k
  | 0 => rfl
  | k + 1 => by simp [num, ev_num k]

@[simp] theorem ev_var (i : Fin n) : PTm.ev ρ (Syn.var i : PTm n) = ρ i := rfl

@[simp] theorem ev_eqb (s t : PTm n) :
    PTm.ev ρ (eqb s t) = if PTm.ev ρ s = PTm.ev ρ t then 1 else 0 := by
  simp only [eqb, ev_monus, ev_add, ev_succ, ev_zero]
  split_ifs with h <;> omega

@[simp] theorem ev_sg (t : PTm n) : PTm.ev ρ (Signum.sg t) = if PTm.ev ρ t = 0 then 0 else 1 := by
  simp only [Signum.sg, ev_monus, ev_succ, ev_zero]
  split_ifs with h <;> omega

theorem ev_lsum : ∀ l : List (PTm n), PTm.ev ρ (lsum l) = (l.map (PTm.ev ρ)).sum
  | [] => rfl
  | t :: l => by simp [lsum, ev_lsum l]

theorem ev_lprod : ∀ l : List (PTm n), PTm.ev ρ (lprod l) = (l.map (PTm.ev ρ)).prod
  | [] => rfl
  | t :: l => by simp [lprod, ev_lprod l]

@[simp] theorem ev_fsum (k : ℕ) (f : Fin k → PTm n) : PTm.ev ρ (fsum k f) = ∑ i, PTm.ev ρ (f i) := by
  simp [fsum, ev_lsum, List.map_ofFn, List.sum_ofFn]

@[simp] theorem ev_fprod (k : ℕ) (f : Fin k → PTm n) :
    PTm.ev ρ (fprod k f) = ∏ i, PTm.ev ρ (f i) := by
  simp [fprod, ev_lprod, List.map_ofFn, List.prod_ofFn]

theorem ev_subst {m : ℕ} (σ : Fin m → PTm n) :
    ∀ t : PTm m, PTm.ev ρ (Syn.subst σ t) = PTm.ev (fun i => PTm.ev ρ (σ i)) t
  | .var i => rfl
  | .app f ts => by
    show PR.ev f (fun i => PTm.ev ρ (Syn.subst σ (ts i))) = PR.ev f (fun i => PTm.ev _ (ts i))
    congr 1; funext i; exact ev_subst σ (ts i)

end Values

/-! ## Products with a vanishing factor, and two -/

theorem fprod_eq_zero {k : ℕ} {f : Fin k → PTm n} (i : Fin k) (h : Γ ⊢[PRAAx] f i ≐ zero) :
    Γ ⊢[PRAAx] fprod k f ≐ zero := by
  apply of_mk
  rw [mk_fprod, Q.mk_zero]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [Q.sound h, Q.mk_zero])

theorem fsum_eq_zero {k : ℕ} {f : Fin k → PTm n} (h : ∀ i, Γ ⊢[PRAAx] f i ≐ zero) :
    Γ ⊢[PRAAx] fsum k f ≐ zero := by
  apply of_mk
  rw [mk_fsum, Q.mk_zero]
  exact Finset.sum_eq_zero (fun i _ => by rw [Q.sound (h i), Q.mk_zero])

theorem fsum_congr {k : ℕ} {f g : Fin k → PTm n} (h : ∀ i, Γ ⊢[PRAAx] f i ≐ g i) :
    Γ ⊢[PRAAx] fsum k f ≐ fsum k g := by
  apply of_mk
  rw [mk_fsum, mk_fsum]
  exact Finset.sum_congr rfl (fun i _ => Q.sound (h i))

theorem fprod_congr {k : ℕ} {f g : Fin k → PTm n} (h : ∀ i, Γ ⊢[PRAAx] f i ≐ g i) :
    Γ ⊢[PRAAx] fprod k f ≐ fprod k g := by
  apply of_mk
  rw [mk_fprod, mk_fprod]
  exact Finset.prod_congr rfl (fun i _ => Q.sound (h i))

theorem ftsum_congr {ι : Type} [Fintype ι] {f g : ι → PTm n} (h : ∀ i, Γ ⊢[PRAAx] f i ≐ g i) :
    Γ ⊢[PRAAx] ftsum f ≐ ftsum g := by
  apply of_mk
  rw [mk_ftsum, mk_ftsum]
  exact Finset.sum_congr rfl (fun i _ => Q.sound (h i))

end LeanProofs.IPRA.Foundations.TermSums

export_ipra Foundations.TermSums (fsum)
