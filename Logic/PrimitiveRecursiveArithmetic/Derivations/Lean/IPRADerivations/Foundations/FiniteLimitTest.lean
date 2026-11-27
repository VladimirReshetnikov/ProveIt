import IPRADerivations.Foundations.FiniteLimits

/-!
# The retention test of a finite limit as a term (`ipra_categorical_methods`, "Finite limits, including equalizers and pullbacks")

Packet: `foundations/ipra_categorical_methods`, Section 4: "Retain a tuple exactly when every
arrow satisfies `D(a)(x_i) = x_j` (L)."

`Foundations/FiniteLimits` proves the universal property of the limit of a finite diagram for
a retention test `K` characterized by (L). Here the test is constructed: the product, over the
arrows, of the equality bits of (L) on the mixed-radix digits of the code. The sizes of the
objects are terms `b_i(y)` of the parameter.

* `eqbProd L R`: the product of the bits `[L_e = R_e]`; `eqbProd_ne`, `eq_of_eqbProd`: it is
  nonzero exactly when `L_e = R_e` for every `e`;
* `subst_eqbProd`, `subst_dig`: substitution commutes with the product and with the digits;
* `Bt`, `Bc`, `testK`, `testK_at`: the sizes, and the test
  `K(n, y) = ∏_e [f_e(digit_{src e}(n), y) = digit_{tgt e}(n)]` with its value at terms;
* `test_sound`, `test_complete`: `K(n, y) ≠ 0` exactly when the digits of `n` satisfy (L);
* `limit_cone`, `limit_factor_lt`, `limit_factor_proj`: the cone equations and the
  factorization of `Foundations/FiniteLimits` for this test, with no hypothesis on it.
  Uniqueness of the mediator is `FiniteLimits.limit_unique`, which needs no property of the
  test.

So for every finite diagram shape (objects, arrows, sources and targets as parameters of the
Lean statements) and all object sizes and arrow terms, the limit `[ℓ]`,
`ℓ = rank (testK) (∏ b_i)`, its cone and its mediators are terms with derived universal
property. Not derived: finite colimits of a general diagram.
-/

namespace LeanProofs.IPRA.Foundations.FiniteLimitTest

open_ipra exports
open LeanProofs.IPRA.Foundations.MixedRadixGrid (prodT code dig)
open LeanProofs.IPRA.Foundations.FilteredEnumeration (rank sel)
open LeanProofs.IPRA.Foundations.FiniteLimits (proj proj_compat factor_lt factor_proj)
open LeanProofs.IPRA.Foundations.BoundedReflection (one_ne_zero)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## A product of equality bits -/

/-- `∏_e [L_e = R_e]`. -/
def eqbProd : {m : ℕ} → (Fin m → PTm k) → (Fin m → PTm k) → PTm k
  | 0, _, _ => one
  | _ + 1, L, R => eqb (L 0) (R 0) * eqbProd (fun e => L e.succ) (fun e => R e.succ)

/-- If every equation holds, the product is not zero. -/
theorem eqbProd_ne : {m : ℕ} → {L R : Fin m → PTm k} → (∀ e, Γ ⊢[PRAAx] L e ≐ R e) →
    (Γ ⊢[PRAAx] neg (eqbProd L R ≐ zero))
  | 0, _, _, _ => .impI (one_ne_zero _ Prf.hyp0)
  | _ + 1, _, _, h =>
    .impI (.impE (eqbProd_ne fun e => h e.succ).wk
      (((one_mul _).eqSymm.eqTrans
        (congrMul (eqb_of_eq (h 0).wk).eqSymm (.eqRefl _))).eqTrans Prf.hyp0))

/-- If the product is not zero, every equation holds. -/
theorem eq_of_eqbProd : {m : ℕ} → {L R : Fin m → PTm k} →
    (Γ ⊢[PRAAx] neg (eqbProd L R ≐ zero)) → ∀ e, Γ ⊢[PRAAx] L e ≐ R e
  | 0, _, _, _, e => e.elim0
  | _ + 1, L, R, h, e => by
    refine Fin.cases ?_ (fun e' => ?_) e
    · refine eq_of_eqb_ne (.impI (.impE h.wk ?_))
      exact (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)
    · refine eq_of_eqbProd (L := fun e => L e.succ) (R := fun e => R e.succ)
        (.impI (.impE h.wk ?_)) e'
      exact (congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)

theorem subst_eqbProd {j : ℕ} (σ : Fin k → PTm j) : {m : ℕ} → (L R : Fin m → PTm k) →
    Syn.subst σ (eqbProd L R) =
      eqbProd (fun e => Syn.subst σ (L e)) (fun e => Syn.subst σ (R e))
  | 0, _, _ => by simp [eqbProd]
  | m + 1, L, R => by
    simp only [eqbProd, PTm.subst_mul, subst_eqb]
    rw [subst_eqbProd σ (fun e => L e.succ) (fun e => R e.succ)]

theorem subst_dig {j : ℕ} (σ : Fin k → PTm j) : {r : ℕ} → (B : Fin r → PTm k) → (n : PTm k) →
    (i : Fin r) →
    Syn.subst σ (dig B n i) = dig (fun i => Syn.subst σ (B i)) (Syn.subst σ n) i
  | 0, _, _, i => i.elim0
  | r + 1, B, n, i => by
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp [dig]
    · simp only [dig, Fin.cases_succ]
      rw [subst_dig σ (fun i => B i.succ) (quo n (B 0)) i']
      simp

/-! ## The test -/

section Test

variable {r m : ℕ} (b : Fin r → PTm 1) (src tgt : Fin m → Fin r) (f : Fin m → PTm 2)

/-- The size of object `i` as a term of the parameter; variables `0 = n`, `1 = y`. -/
def Bt (i : Fin r) : PTm 2 := Syn.subst ![var 1] (b i)

/-- The size of object `i` at a parameter. -/
def Bc (y : PTm k) (i : Fin r) : PTm k := Syn.subst ![y] (b i)

theorem Bt_at (n y : PTm k) (i : Fin r) : Syn.subst ![n, y] (Bt b i) = Bc b y i := by
  simp only [Bt, Bc, Syn.subst_subst]
  congr 1; funext l; fin_cases l; rfl

/-- (L) as a term: `K(n, y) = ∏_e [f_e(digit_{src e}(n), y) = digit_{tgt e}(n)]`. -/
def testK : PTm 2 :=
  eqbProd (fun e => inst2 (f e) (dig (Bt b) (var 0) (src e)) (var 1))
    (fun e => dig (Bt b) (var 0) (tgt e))

theorem testK_at (n y : PTm k) :
    inst2 (testK b src tgt f) n y =
      eqbProd (fun e => inst2 (f e) (dig (Bc b y) n (src e)) y)
        (fun e => dig (Bc b y) n (tgt e)) := by
  have hB : (fun i => Syn.subst ![n, y] (Bt b i)) = Bc b y := funext (Bt_at b n y)
  show Syn.subst ![n, y] (testK b src tgt f) = _
  unfold testK
  rw [subst_eqbProd]
  congr 1
  · funext e
    rw [subst_inst2, subst_dig, hB]
    rfl
  · funext e
    rw [subst_dig, hB]
    rfl

/-- A retained code satisfies (L). -/
theorem test_sound {n y : PTm k}
    (h : Γ ⊢[PRAAx] neg (inst2 (testK b src tgt f) n y ≐ zero)) (e : Fin m) :
    Γ ⊢[PRAAx] inst2 (f e) (dig (Bc b y) n (src e)) y ≐ dig (Bc b y) n (tgt e) := by
  rw [testK_at] at h
  exact eq_of_eqbProd h e

/-- A code satisfying (L) is retained. -/
theorem test_complete {n y : PTm k}
    (h : ∀ e, Γ ⊢[PRAAx] inst2 (f e) (dig (Bc b y) n (src e)) y ≐ dig (Bc b y) n (tgt e)) :
    Γ ⊢[PRAAx] neg (inst2 (testK b src tgt f) n y ≐ zero) := by
  rw [testK_at]
  exact eqbProd_ne h

/-- The cone equations of the limit. -/
theorem limit_cone {j y : PTm k}
    (hj : Γ ⊢[PRAAx] lt j (rank (testK b src tgt f) (prodT (Bc b y)) y)) (e : Fin m) :
    Γ ⊢[PRAAx] inst2 (f e) (proj (testK b src tgt f) (Bc b y) y (src e) j) y ≐
      proj (testK b src tgt f) (Bc b y) y (tgt e) j :=
  proj_compat (testK b src tgt f) (Bc b y) y src tgt f
    (fun _ h e => test_sound b src tgt f h e) hj e

/-- The mediator of a compatible tuple is an index of the limit. -/
theorem limit_factor_lt {y : PTm k}
    (hB : ∀ i, Γ ⊢[PRAAx] Bc b y i ≐ succ (pred (Bc b y i))) {c : Fin r → PTm k}
    (hlt : ∀ i, Γ ⊢[PRAAx] lt (c i) (Bc b y i))
    (hcomp : ∀ e, Γ ⊢[PRAAx] inst2 (f e) (c (src e)) y ≐ c (tgt e)) :
    Γ ⊢[PRAAx] lt (rank (testK b src tgt f) (code (Bc b y) c) y)
      (rank (testK b src tgt f) (prodT (Bc b y)) y) :=
  factor_lt (testK b src tgt f) (Bc b y) y src tgt f
    (fun _ h => test_complete b src tgt f h) hB hlt hcomp

/-- The factorization through the limit. -/
theorem limit_factor_proj {y : PTm k}
    (hB : ∀ i, Γ ⊢[PRAAx] Bc b y i ≐ succ (pred (Bc b y i))) {c : Fin r → PTm k}
    (hlt : ∀ i, Γ ⊢[PRAAx] lt (c i) (Bc b y i))
    (hcomp : ∀ e, Γ ⊢[PRAAx] inst2 (f e) (c (src e)) y ≐ c (tgt e)) (i : Fin r) :
    Γ ⊢[PRAAx] proj (testK b src tgt f) (Bc b y) y i
        (rank (testK b src tgt f) (code (Bc b y) c) y) ≐ c i :=
  factor_proj (testK b src tgt f) (Bc b y) y src tgt f
    (fun _ h => test_complete b src tgt f h) hB hlt hcomp i

end Test

end LeanProofs.IPRA.Foundations.FiniteLimitTest
