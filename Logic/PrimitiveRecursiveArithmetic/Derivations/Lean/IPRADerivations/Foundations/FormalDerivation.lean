import IPRADerivations.Core.PolynomialImplications

/-!
# Formal derivations of polynomial expressions and of their fractions

A reusable piece of the embedding framework for differential calculations with rational
functions (used for `geometry/four_metrics_ipra_2026-11-15`, whose curvature computations are
"a finite second-jet calculation": the unknown radial function and its derivatives are
independent indeterminates `d, v, w` with `∂_r d = v`, `∂_r v = w`).

* `ZExp.der δ`: the derivation of the polynomial expressions (`Core/PolynomialImplications.ZExp`)
  with prescribed values `δ i` on the variables, extended by the sum rule and the Leibniz rule
  (`der_add`, `der_mul`, `der_neg`, `der_sub`, `der_numeral`, `der_pow_succ`);
* `ZExp.Frac`: a fraction `num / den` of polynomial expressions, with `+`, `*`, `−`, the
  embedding `ofZ`, the half `half`, and the derivative `Frac.d δ` by the quotient rule
  `(n/m)′ = (n′ m − n m′)/m²`;
* `Frac.eqn f g`: the equation `f = g` cleared of denominators, `f.num · g.den = g.num · f.den`,
  a pair of expressions for `ZExp.derive_imp`. An identity of rational functions is derived as
  this polynomial identity, certified in every commutative ring;
* `leibniz`, `quotient_rule`: the product rule `(fg)′ = f′ g + f g′` for fractions and the
  rule `(1/m)′ = −m′/m²`, as closed sentences of iPRA for arbitrary numerators, denominators
  and values of their derivatives (a check of the definitions).

A derivation is a syntactic operation: it differentiates the expression as written. No
function is evaluated and no limit is taken.
-/

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA

namespace ZExp

variable {k : ℕ}

/-- The derivation of the polynomial expressions with the values `δ i` on the variables. -/
def der (δ : Fin k → ZExp k) : ZExp k → ZExp k
  | var i => δ i
  | lit _ => 0
  | add a b => der δ a + der δ b
  | mul a b => der δ a * b + a * der δ b
  | neg a => -der δ a

section Rules

variable (δ : Fin k → ZExp k) (a b : ZExp k)

@[simp] theorem der_var (i : Fin k) : der δ (var i) = δ i := rfl
@[simp] theorem der_add : der δ (a + b) = der δ a + der δ b := rfl
@[simp] theorem der_mul : der δ (a * b) = der δ a * b + a * der δ b := rfl
@[simp] theorem der_neg : der δ (-a) = -der δ a := rfl
@[simp] theorem der_sub : der δ (a - b) = der δ a - der δ b := rfl
@[simp] theorem der_ofNat (c : ℕ) : der δ (OfNat.ofNat c : ZExp k) = 0 := rfl
@[simp] theorem der_zero : der δ (0 : ZExp k) = 0 := rfl
@[simp] theorem der_one : der δ (1 : ZExp k) = 0 := rfl
@[simp] theorem der_numeral (c : ℕ) [c.AtLeastTwo] :
    der δ (no_index (OfNat.ofNat c) : ZExp k) = 0 := rfl
@[simp] theorem der_pow_zero : der δ (a ^ 0) = 0 := rfl
@[simp] theorem der_pow_succ (m : ℕ) :
    der δ (a ^ (m + 1)) = der δ (a ^ m) * a + a ^ m * der δ a := rfl

end Rules

/-- A fraction of polynomial expressions. -/
structure Frac (k : ℕ) where
  /-- The numerator. -/
  num : ZExp k
  /-- The denominator. -/
  den : ZExp k

namespace Frac

instance : Add (Frac k) := ⟨fun f g => ⟨f.num * g.den + g.num * f.den, f.den * g.den⟩⟩
instance : Mul (Frac k) := ⟨fun f g => ⟨f.num * g.num, f.den * g.den⟩⟩
instance : Neg (Frac k) := ⟨fun f => ⟨-f.num, f.den⟩⟩
instance : Sub (Frac k) := ⟨fun f g => ⟨f.num * g.den - g.num * f.den, f.den * g.den⟩⟩

/-- A polynomial expression as a fraction. -/
def ofZ (e : ZExp k) : Frac k := ⟨e, 1⟩

/-- `f / 2`. -/
def half (f : Frac k) : Frac k := ⟨f.num, 2 * f.den⟩

/-- The derivative by the quotient rule. -/
def d (δ : Fin k → ZExp k) (f : Frac k) : Frac k :=
  ⟨der δ f.num * f.den - f.num * der δ f.den, f.den * f.den⟩

/-- The equation `f = g` cleared of denominators. -/
def eqn (f g : Frac k) : ZExp k × ZExp k := (f.num * g.den, g.num * f.den)

section Rules

variable (δ : Fin k → ZExp k) (f g : Frac k) (e : ZExp k)

@[simp] theorem add_num : (f + g).num = f.num * g.den + g.num * f.den := rfl
@[simp] theorem add_den : (f + g).den = f.den * g.den := rfl
@[simp] theorem mul_num : (f * g).num = f.num * g.num := rfl
@[simp] theorem mul_den : (f * g).den = f.den * g.den := rfl
@[simp] theorem neg_num : (-f).num = -f.num := rfl
@[simp] theorem neg_den : (-f).den = f.den := rfl
@[simp] theorem sub_num : (f - g).num = f.num * g.den - g.num * f.den := rfl
@[simp] theorem sub_den : (f - g).den = f.den * g.den := rfl
@[simp] theorem ofZ_num : (ofZ e).num = e := rfl
@[simp] theorem ofZ_den : (ofZ e).den = 1 := rfl
@[simp] theorem half_num : (half f).num = f.num := rfl
@[simp] theorem half_den : (half f).den = 2 * f.den := rfl
@[simp] theorem d_num : (d δ f).num = der δ f.num * f.den - f.num * der δ f.den := rfl
@[simp] theorem d_den : (d δ f).den = f.den * f.den := rfl
@[simp] theorem eqn_fst : (eqn f g).1 = f.num * g.den := rfl
@[simp] theorem eqn_snd : (eqn f g).2 = g.num * f.den := rfl

end Rules

end Frac

end ZExp

end LeanProofs.IPRA

/-- Start a certificate for an identity of fractions with formal derivatives:
`frac_poly R ρ h [defs]` unfolds the listed definitions together with the rules of
`ZExp.der` and `ZExp.Frac`, and normalizes the evaluations. -/
syntax "frac_poly " ident ident ident (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| frac_poly $R:ident $ρ:ident $h:ident) =>
    `(tactic| ipra_poly $R $ρ $h [LeanProofs.IPRA.ZExp.Frac.eqn,
        LeanProofs.IPRA.ZExp.Frac.add_num, LeanProofs.IPRA.ZExp.Frac.add_den,
        LeanProofs.IPRA.ZExp.Frac.mul_num, LeanProofs.IPRA.ZExp.Frac.mul_den,
        LeanProofs.IPRA.ZExp.Frac.neg_num, LeanProofs.IPRA.ZExp.Frac.neg_den,
        LeanProofs.IPRA.ZExp.Frac.sub_num, LeanProofs.IPRA.ZExp.Frac.sub_den,
        LeanProofs.IPRA.ZExp.Frac.ofZ_num, LeanProofs.IPRA.ZExp.Frac.ofZ_den,
        LeanProofs.IPRA.ZExp.Frac.half_num, LeanProofs.IPRA.ZExp.Frac.half_den,
        LeanProofs.IPRA.ZExp.Frac.d_num, LeanProofs.IPRA.ZExp.Frac.d_den,
        LeanProofs.IPRA.ZExp.der_var, LeanProofs.IPRA.ZExp.der_add,
        LeanProofs.IPRA.ZExp.der_mul, LeanProofs.IPRA.ZExp.der_neg,
        LeanProofs.IPRA.ZExp.der_sub, LeanProofs.IPRA.ZExp.der_ofNat,
        LeanProofs.IPRA.ZExp.der_zero, LeanProofs.IPRA.ZExp.der_one,
        LeanProofs.IPRA.ZExp.der_numeral,
        LeanProofs.IPRA.ZExp.der_pow_zero, LeanProofs.IPRA.ZExp.der_pow_succ])
  | `(tactic| frac_poly $R:ident $ρ:ident $h:ident [$ls,*]) =>
    `(tactic| ipra_poly $R $ρ $h [$ls,*, LeanProofs.IPRA.ZExp.Frac.eqn,
        LeanProofs.IPRA.ZExp.Frac.add_num, LeanProofs.IPRA.ZExp.Frac.add_den,
        LeanProofs.IPRA.ZExp.Frac.mul_num, LeanProofs.IPRA.ZExp.Frac.mul_den,
        LeanProofs.IPRA.ZExp.Frac.neg_num, LeanProofs.IPRA.ZExp.Frac.neg_den,
        LeanProofs.IPRA.ZExp.Frac.sub_num, LeanProofs.IPRA.ZExp.Frac.sub_den,
        LeanProofs.IPRA.ZExp.Frac.ofZ_num, LeanProofs.IPRA.ZExp.Frac.ofZ_den,
        LeanProofs.IPRA.ZExp.Frac.half_num, LeanProofs.IPRA.ZExp.Frac.half_den,
        LeanProofs.IPRA.ZExp.Frac.d_num, LeanProofs.IPRA.ZExp.Frac.d_den,
        LeanProofs.IPRA.ZExp.der_var, LeanProofs.IPRA.ZExp.der_add,
        LeanProofs.IPRA.ZExp.der_mul, LeanProofs.IPRA.ZExp.der_neg,
        LeanProofs.IPRA.ZExp.der_sub, LeanProofs.IPRA.ZExp.der_ofNat,
        LeanProofs.IPRA.ZExp.der_zero, LeanProofs.IPRA.ZExp.der_one,
        LeanProofs.IPRA.ZExp.der_numeral,
        LeanProofs.IPRA.ZExp.der_pow_zero, LeanProofs.IPRA.ZExp.der_pow_succ])

namespace LeanProofs.IPRA.Foundations.FormalDerivation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

/-! ## The rules for arbitrary numerators, denominators and derivative values

Variables `0, 1` are the numerator and the denominator of `f`, `2, 3` those of `g`, and
`4, …, 7` the values of their derivatives. -/

/-- The derivation with the values `var (i + 4)` on the first four variables. -/
def δ₈ : Fin 8 → ZExp 8
  | ⟨0, _⟩ => var 4
  | ⟨1, _⟩ => var 5
  | ⟨2, _⟩ => var 6
  | ⟨3, _⟩ => var 7
  | _ => 0

theorem δ₈_0 : δ₈ 0 = var 4 := rfl
theorem δ₈_1 : δ₈ 1 = var 5 := rfl
theorem δ₈_2 : δ₈ 2 = var 6 := rfl
theorem δ₈_3 : δ₈ 3 = var 7 := rfl

/-- `f = var 0 / var 1`. -/
abbrev f₈ : Frac 8 := ⟨var 0, var 1⟩
/-- `g = var 2 / var 3`. -/
abbrev g₈ : Frac 8 := ⟨var 2, var 3⟩

/-- The product rule for fractions: `(f g)′ = f′ g + f g′`. -/
theorem leibniz :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp [] (Frac.eqn (Frac.d δ₈ (f₈ * g₈)) (Frac.d δ₈ f₈ * g₈ + f₈ * Frac.d δ₈ g₈))) :=
  derive_imp _ _ (by frac_poly R ρ h [δ₈_0, δ₈_1, δ₈_2, δ₈_3]; ring)

/-- The sum rule for fractions: `(f + g)′ = f′ + g′`. -/
theorem sum_rule :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp [] (Frac.eqn (Frac.d δ₈ (f₈ + g₈)) (Frac.d δ₈ f₈ + Frac.d δ₈ g₈))) :=
  derive_imp _ _ (by frac_poly R ρ h [δ₈_0, δ₈_1, δ₈_2, δ₈_3]; ring)

/-- `(1/m)′ = −m′/m²`. -/
theorem quotient_rule :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp [] (Frac.eqn (Frac.d δ₈ ⟨1, var 1⟩) ⟨-var 5, var 1 ^ 2⟩)) :=
  derive_imp _ _ (by frac_poly R ρ h [δ₈_0, δ₈_1, δ₈_2, δ₈_3]; ring)

end LeanProofs.IPRA.Foundations.FormalDerivation
