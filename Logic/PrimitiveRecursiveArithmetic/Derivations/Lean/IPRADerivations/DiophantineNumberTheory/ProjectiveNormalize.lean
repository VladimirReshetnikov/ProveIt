import IPRADerivations.DiophantineNumberTheory.Coprime
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# Primitive representatives on the projective line

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Lemma `lem:normalize` ("Primitive
representatives"): "Every nonzero integral vector `v` has a primitive representative `norm(v)`, obtained by
dividing by `g = gcd(|v_0|, …, |v_n|)` ... Two such representatives of the same rational projective point are
equal. Normalization is primitive recursive and never increases the maximum absolute coordinate." The proof:
"Suppose primitive vectors `v, w` satisfy `v_i w_j = v_j w_i` ... cancellation gives `w_i = a v_i` ... As `w`
is primitive, `|a| = 1`."

Derived here for points of `P^1` with natural coordinates and first coordinate `a ≥ 1` (the sign convention is
then automatic):

* `norm_primitive`: with `g = gcd(a, b)`, `a = g (a/g)`, `b = g (b/g)` and `gcd(a/g, b/g) = 1`
  (`Coprime.coprime_quotients`);
* `norm_le`: `a/g ≤ a` and `b/g ≤ b`, so the height does not increase;
* `norm_unique`: primitive `(a, b)`, `(c, d)` with `a, c ≥ 1` and `a d = b c` are equal (`a ∣ bc` and
  `gcd(a, b) = 1` give `a ∣ c` by `Coprime.gauss`, symmetrically `c ∣ a`, then `a d = b a` cancels);
* `norm_class`: two proportional vectors `a d = b c` (`a, c ≥ 1`) have the same normalization.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.ProjectiveNormalize

open_ipra
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd' dvd_of_eq' dvd_le' gcd_dvd' gauss
  coprime_quotients pos_of_eq_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Foundations.ChineseRemainder (gcd_pos)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The normalized coordinates `a/g`, `b/g`, `g = gcd(a, b)`. -/
abbrev nA (a b : PTm k) : PTm k := quo a (gcd a b)
abbrev nB (a b : PTm k) : PTm k := quo b (gcd a b)

/-- `a = g (a/g)`, `b = g (b/g)` and `gcd(a/g, b/g) = 1`. -/
theorem norm_primitive {a b : PTm k} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) :
    Γ ⊢[PRAAx] (a ≐ gcd a b * nA a b) ⋏ (b ≐ gcd a b * nB a b) ⋏ (gcd (nA a b) (nB a b) ≐ one) := by
  have hg := gcd_pos (B := b) ha
  have hd := gcd_dvd' (b := b) ha
  exact Prf.andI (eq_of_dvd' hg (Prf.andE₁ hd)) (Prf.andI (eq_of_dvd' hg (Prf.andE₂ hd)) (coprime_quotients ha))

theorem quo_le_of {x g q : PTm k} (hg : Γ ⊢[PRAAx] g ≐ succ (pred g)) (h : Γ ⊢[PRAAx] x ≐ g * q) :
    Γ ⊢[PRAAx] le q x := by
  have e := natEq h; have eg := natEq hg
  ipra_le 𝔞 (pred g) * 𝔞 q using linear_combination e + 𝔞 q * eg

/-- Normalization does not increase the coordinates: `a/g ≤ a`, `b/g ≤ b`. -/
theorem norm_le {a b : PTm k} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) :
    Γ ⊢[PRAAx] le (nA a b) a ⋏ le (nB a b) b := by
  have hg := gcd_pos (B := b) ha
  have np := norm_primitive (b := b) ha
  exact Prf.andI (quo_le_of hg (Prf.andE₁ np)) (quo_le_of hg (Prf.andE₁ (Prf.andE₂ np)))

/-- Two primitive representatives of the same point are equal. -/
theorem norm_unique {a b c d : PTm k} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hc : Γ ⊢[PRAAx] c ≐ succ (pred c))
    (hab : Γ ⊢[PRAAx] gcd a b ≐ one) (hcd : Γ ⊢[PRAAx] gcd c d ≐ one) (h : Γ ⊢[PRAAx] a * d ≐ b * c) :
    Γ ⊢[PRAAx] (a ≐ c) ⋏ (b ≐ d) := by
  have d1 : Γ ⊢[PRAAx] dvd a (b * c) := dvd_of_eq' ha (w := d) h.eqSymm
  have ac : Γ ⊢[PRAAx] dvd a c := gauss ha hab d1
  have d2 : Γ ⊢[PRAAx] dvd c (d * a) := dvd_of_eq' hc (w := b) (by
    have e := natEq h
    apply deriveNat; ipra_simps; linear_combination e)
  have ca : Γ ⊢[PRAAx] dvd c a := gauss hc hcd d2
  have eac : Γ ⊢[PRAAx] a ≐ c := le_antisymm (dvd_le' ha ac hc) (dvd_le' hc ca ha)
  refine Prf.andI eac ?_
  refine (mul_cancel ha ?_).eqSymm
  have e := natEq h; have e' := natEq eac
  apply deriveNat; ipra_simps; linear_combination e - 𝔞 b * e'

/-- Proportional vectors have the same normalization. -/
theorem norm_class {a b c d : PTm k} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hc : Γ ⊢[PRAAx] c ≐ succ (pred c))
    (h : Γ ⊢[PRAAx] a * d ≐ b * c) :
    Γ ⊢[PRAAx] (nA a b ≐ nA c d) ⋏ (nB a b ≐ nB c d) := by
  have hg := gcd_pos (B := b) ha
  have hh := gcd_pos (B := d) hc
  have n1 := norm_primitive (b := b) ha
  have n2 := norm_primitive (b := d) hc
  have eA := natEq (Prf.andE₁ n1); have eB := natEq (Prf.andE₁ (Prf.andE₂ n1))
  have eC := natEq (Prf.andE₁ n2); have eD := natEq (Prf.andE₁ (Prf.andE₂ n2))
  have pA : Γ ⊢[PRAAx] nA a b ≐ succ (pred (nA a b)) := pos_of_eq_mul ha (Prf.andE₁ n1)
  have pC : Γ ⊢[PRAAx] nA c d ≐ succ (pred (nA c d)) := pos_of_eq_mul hc (Prf.andE₁ n2)
  have hgh := pos_mul hg hh
  have prop : Γ ⊢[PRAAx] nA a b * nB c d ≐ nB a b * nA c d := by
    refine mul_cancel hgh ?_
    ipra_lc natEq h - 𝔞 a * eD - 𝔞 (gcd c d) * 𝔞 (nB c d) * eA + 𝔞 b * eC + 𝔞 (gcd c d) * 𝔞 (nA c d) * eB
  exact norm_unique pA pC (Prf.andE₂ (Prf.andE₂ n1)) (Prf.andE₂ (Prf.andE₂ n2)) prop

end LeanProofs.IPRA.DiophantineNumberTheory.ProjectiveNormalize
