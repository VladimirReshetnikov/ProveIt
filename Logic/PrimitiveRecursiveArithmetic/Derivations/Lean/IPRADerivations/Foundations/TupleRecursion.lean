import IPRADerivations.Core.Pairing
import IPRADerivations.Core.Header

/-!
# Simultaneous primitive recursion of finitely many sequences

`Core/Pairing` defines two sequences by simultaneous recursion (`sim₁`, `sim₂`). A vector-valued recursion of a
fixed dimension, such as the exact Euler array of a linear system, needs `m` sequences at once. This module codes
an `m`-tuple of terms by nested pairs and defines the `m` sequences by one primitive recursion on the code.

* `tup f = ⟨f 0, ⟨f 1, … ⟨f (m−1), 0⟩⟩⟩` and its projections `prj i`, with `prj_tup : prj i (tup f) = f i`,
  the congruences `congrPrj`, `congrTup` and the substitution lemmas `subst_tup`, `subst_prj`.
* A step is given as a function on terms (`Step m k`): from the recursion variable `y`, the `m` current values
  and `k` parameters it returns the `m` next values, and it commutes with substitution (`Step.nat`), so that it is
  the instance of one fixed tuple of terms. This avoids arithmetic on variable indices.
* `vrec S i y init xs` is the `i`-th sequence at `y`, started from the values `init` and with the parameters
  `xs`. The initial values are arguments of the recursion (the program takes the code `tup init` as a parameter),
  so they may be arbitrary terms of the context. The defining equations are

      vrec S i 0 init xs       = init i                                         (`vrec_zero`)
      vrec S i (y + 1) init xs = S.fn y (fun l => vrec S l y init xs) xs i      (`vrec_succ`)

  with the congruence `congrVrec` and the substitution lemma `subst_vrec`.
-/

namespace LeanProofs.IPRA.Foundations.TupleRecursion

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Tuples -/

theorem congrPairT {a a' b b' : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ a') (h₂ : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] pairT a b ≐ pairT a' b' := by
  unfold pairT
  exact congrAdd (congrMul (congrAdd h₁ h₂) (congrAdd h₁ h₂)) h₁

/-- The code of an `m`-tuple, by nested pairs. -/
def tup : {m : ℕ} → (Fin m → PTm n) → PTm n
  | 0, _ => zero
  | _ + 1, f => pairT (f 0) (tup fun i => f i.succ)

/-- The `i`-th component of the code of an `m`-tuple. -/
def prj : {m : ℕ} → Fin m → PTm n → PTm n
  | 0, i, _ => i.elim0
  | _ + 1, i, z => Fin.cases (fstT z) (fun j => prj j (sndT z)) i

@[simp] theorem prj_zero {m : ℕ} (z : PTm n) : prj (0 : Fin (m + 1)) z = fstT z := rfl

@[simp] theorem prj_succ {m : ℕ} (j : Fin m) (z : PTm n) : prj j.succ z = prj j (sndT z) := by
  cases j; rfl

@[simp] theorem subst_tup {k : ℕ} (σ : Fin n → PTm k) : {m : ℕ} → (f : Fin m → PTm n) →
    Syn.subst σ (tup f) = tup fun i => Syn.subst σ (f i)
  | 0, _ => by simp only [tup, ConciseIPRA.PTm.subst_zero]
  | m + 1, f => by
    simp only [tup, subst_pairT]
    rw [subst_tup σ fun i => f i.succ]

@[simp] theorem subst_prj {k : ℕ} (σ : Fin n → PTm k) : {m : ℕ} → (i : Fin m) → (z : PTm n) →
    Syn.subst σ (prj i z) = prj i (Syn.subst σ z)
  | 0, i, _ => i.elim0
  | m + 1, i, z => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [prj_zero, subst_fstT]
    · simp only [prj_succ]
      rw [subst_prj σ j (sndT z), subst_sndT]

theorem congrPrj : {m : ℕ} → (i : Fin m) → {z z' : PTm n} → (Γ ⊢[PRAAx] z ≐ z') →
    (Γ ⊢[PRAAx] prj i z ≐ prj i z')
  | 0, i, _, _, _ => i.elim0
  | m + 1, i, z, z', h => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact congrFst h
    · simp only [prj_succ]
      exact congrPrj j (congrSnd h)

theorem congrTup : {m : ℕ} → {f g : Fin m → PTm n} → (∀ i, Γ ⊢[PRAAx] f i ≐ g i) →
    (Γ ⊢[PRAAx] tup f ≐ tup g)
  | 0, _, _, _ => .eqRefl _
  | _ + 1, _, _, h => congrPairT (h 0) (congrTup fun i => h i.succ)

/-- The components of a tuple code. -/
theorem prj_tup : {m : ℕ} → (f : Fin m → PTm n) → (i : Fin m) → (Γ ⊢[PRAAx] prj i (tup f) ≐ f i)
  | 0, _, i => i.elim0
  | m + 1, f, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact fst_pair _ _
    · simp only [prj_succ]
      exact (congrPrj j (snd_pair _ _)).eqTrans (prj_tup (fun i => f i.succ) j)

/-! ## The recursion -/

/-- The step of an `m`-fold simultaneous recursion with `k` parameters: a function on terms that commutes with
substitution. `fn y s p i` is the `i`-th next value, from the recursion variable `y`, the current values `s` and
the parameters `p`. -/
structure Step (m k : ℕ) where
  fn : {N : ℕ} → PTm N → (Fin m → PTm N) → (Fin k → PTm N) → Fin m → PTm N
  nat : ∀ {N N' : ℕ} (σ : Fin N → PTm N') (y : PTm N) (s : Fin m → PTm N) (p : Fin k → PTm N) (i : Fin m),
    Syn.subst σ (fn y s p i) =
      fn (Syn.subst σ y) (fun l => Syn.subst σ (s l)) (fun j => Syn.subst σ (p j)) i

variable {m k : ℕ}

/-- The step term: variables `0 = y`, `1 =` the code of the current values, `2 =` the initial code (unused),
`3, … =` the parameters. -/
def stepTm (S : Step m k) : PTm (k + 3) :=
  tup fun i => S.fn (var 0) (fun l => prj l (var (0 : Fin (k + 2)).succ)) (fun j => var j.succ.succ.succ) i

/-- The symbol computing the code of the `m` values at `y`, from the initial code and the parameters. -/
def recF (S : Step m k) : PR (k + 2) := recDef (var 0 : PTm (k + 1)) (stepTm S)

/-- The code of the `m` values at `y`, started from the code `c`. -/
def code (S : Step m k) (y c : PTm n) (xs : Fin k → PTm n) : PTm n :=
  app (recF S) (Fin.cases y (Fin.cases c xs : Fin (k + 1) → PTm n) : Fin (k + 2) → PTm n)

/-- The `i`-th of the `m` simultaneously defined sequences at `y`. -/
def vrec (S : Step m k) (i : Fin m) (y : PTm n) (init : Fin m → PTm n) (xs : Fin k → PTm n) : PTm n :=
  prj i (code S y (tup init) xs)

theorem code_zero (S : Step m k) (c : PTm n) (xs : Fin k → PTm n) : Γ ⊢[PRAAx] code S zero c xs ≐ c := by
  have h := rec_zero (Γ := Γ) (var 0 : PTm (k + 1)) (stepTm S) (Fin.cases c xs : Fin (k + 1) → PTm n)
  rw [Syn.subst_var] at h
  exact h

theorem code_succ (S : Step m k) (y c : PTm n) (xs : Fin k → PTm n) :
    Γ ⊢[PRAAx] code S (succ y) c xs ≐ tup fun i => S.fn y (fun l => prj l (code S y c xs)) xs i := by
  have h := rec_succ (Γ := Γ) (var 0 : PTm (k + 1)) (stepTm S) y (Fin.cases c xs : Fin (k + 1) → PTm n)
  rw [stepTm, subst_tup] at h
  simp only [S.nat, subst_prj, Syn.subst_var, Fin.cases_zero, Fin.cases_succ] at h
  exact h

theorem vrec_zero (S : Step m k) (i : Fin m) (init : Fin m → PTm n) (xs : Fin k → PTm n) :
    Γ ⊢[PRAAx] vrec S i zero init xs ≐ init i :=
  (congrPrj i (code_zero S (tup init) xs)).eqTrans (prj_tup init i)

theorem vrec_succ (S : Step m k) (i : Fin m) (y : PTm n) (init : Fin m → PTm n) (xs : Fin k → PTm n) :
    Γ ⊢[PRAAx] vrec S i (succ y) init xs ≐ S.fn y (fun l => vrec S l y init xs) xs i :=
  (congrPrj i (code_succ S y (tup init) xs)).eqTrans (prj_tup _ i)

@[simp] theorem subst_vrec {N : ℕ} (σ : Fin n → PTm N) (S : Step m k) (i : Fin m) (y : PTm n)
    (init : Fin m → PTm n) (xs : Fin k → PTm n) :
    Syn.subst σ (vrec S i y init xs) =
      vrec S i (Syn.subst σ y) (fun l => Syn.subst σ (init l)) fun j => Syn.subst σ (xs j) := by
  simp only [vrec, code, subst_prj, PTm.subst_app]
  congr 2; funext j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
  · rfl
  · simp only [Fin.cases_succ, Fin.cases_zero, subst_tup]
  · rfl

theorem congrVrec (S : Step m k) (i : Fin m) {y y' : PTm n} {init init' : Fin m → PTm n}
    {xs xs' : Fin k → PTm n} (hy : Γ ⊢[PRAAx] y ≐ y') (hi : ∀ l, Γ ⊢[PRAAx] init l ≐ init' l)
    (hx : ∀ j, Γ ⊢[PRAAx] xs j ≐ xs' j) : Γ ⊢[PRAAx] vrec S i y init xs ≐ vrec S i y' init' xs' :=
  congrPrj i (congrApp _ fun j => by
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
    · exact hy
    · exact congrTup hi
    · exact hx j)

end LeanProofs.IPRA.Foundations.TupleRecursion
