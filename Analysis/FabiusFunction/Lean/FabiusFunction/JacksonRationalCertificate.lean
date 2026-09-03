import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Jackson's six-variable rational certificate

This file proves, in full, the algebraic identity behind Jackson's terminating very-well-poised
`₈φ₇` summation.  Writing `Π(x₁, …, x_r) = ∏ (1 - x_i)`, the identity is

```
1 - Π(B, C, D, E, F, A³/(BCDEF)) / Π(A/B, A/C, A/D, A/E, A/F, BCDEF/A²)
  =  Π(A, D, A²/(BCDE), A²/(BCDF), A²/(BDEF), A²/(CDEF))
       / Π(A/B, A/C, A/E, A/F, A²/(BCDEF), A³/(BCD²EF))
     × [ 1 - Π(A/(BD), A/(CD), A/(DE), A/(DF), A²/(BCDEF), A³/(BCDEF))
             / Π(1/D, A/D, A²/(BCDE), A²/(BCDF), A²/(BDEF), A²/(CDEF)) ].
```

## Relation to the source

The statement is the monograph's `qg:lem-jackson-rational-certificate`, transcribed factor by
factor (equation `qg:eq:jackson-rational`).  The source states it in the rational-function field
`ℚ(A, B, C, D, E, F)` and then asserts, as a corollary, that it survives every specialization to
a field in which all displayed rational expressions are defined.  Here the specialized form *is*
the statement: `jackson_rational_certificate` holds over an arbitrary field `K` under exactly
the eighteen hypotheses saying that the displayed expressions are defined, namely

* `A, B, C, D, E, F ≠ 0` (needed for `A/B`, `1/D`, `A³/(BCDEF)`, … — the source leaves these
  tacit, but every displayed expression already requires them);
* `B - A, C - A, D - A, E - A, F - A ≠ 0` and `A² - BCDEF ≠ 0` (the left-hand denominator);
* `D - 1 ≠ 0`, `BCDE - A² ≠ 0`, `BCDF - A² ≠ 0`, `BDEF - A² ≠ 0`, `CDEF - A² ≠ 0` (the bracket's
  denominator) and `BCD²EF - A³ ≠ 0` (the prefactor's denominator).

## What is *not* covered

* Jackson's terminating very-well-poised `₈φ₇` sum (`qg:thm-jackson-8phi7`) and the `₆φ₅`
  corollary (`qg:cor-jackson-6phi5`).  This module supplies only the rational certificate; the
  induction additionally needs the shifted-factorial ratio calculus, the product quotient, the
  `k = n+1` boundary case and the telescoping assembly (`Fabius.euler_telescoping`).
* The *route* of the printed proof.  The source argues through a seed transformation
  `J = R_J · (J ∘ σ)`, the substitution `σ`, the factor `λ = B²C²D²(A-1)/(A(A² - BCD))` and a
  Laurent-coefficient computation in the variable `F`.  That route is replaced here by two
  division-free polynomial identities (`jacksonCertNum_left`, `jacksonCertNum_shift`); nothing
  about `σ`, `λ`, `U`, `V` or `Δᵢ` is formalized.  A side benefit: `λ` has denominator
  `A(A² - BCD)`, so a transcription of the printed route would have to carry `A² ≠ BCD`; the
  route taken here does not.

## Stronger than the source

Both sides of `qg:eq:jackson-rational` collapse to one closed form driven by a single degree-11
polynomial `jacksonCertNum`:

```
LHS = RHS = (1 - A) · Q / ((B-A)(C-A)(D-A)(E-A)(F-A)(A² - BCDEF)).
```

`jackson_certificate_closed_form` proves this for the left-hand side using only twelve of the
eighteen definedness hypotheses: it needs neither `D ≠ 1`, nor `BCD²EF ≠ A³`, nor the four
conditions `BCDE, BCDF, BDEF, CDEF ≠ A²`.  At those six loci the source's right-hand side is a
genuine `0/0` (at `D = 1`, for instance, the prefactor carries `1 - D = 0` while the bracket's
denominator carries `1 - 1/D = 0`), whereas the left-hand side and the closed form remain
defined and equal.  The closed form is also the shape the `₈φ₇` induction consumes.

The two polynomial cores hold over an arbitrary commutative ring (characteristic `2` and
non-domains included), not merely over a field of characteristic `0`.  For the same reason
`jackson_prefactor_closed_form` is stated with only the five hypotheses its proof uses.

## Main declarations

* `jacksonCertNum` — the degree-11 numerator `Q(A; B, C, D, E, F)`, symmetric in `B, C, D, E, F`.
* `jacksonCertNum_left` — `(B-A)⋯(F-A)(A² - BCDEF) - A²(1-B)⋯(1-F)(BCDEF - A³) = (1-A)Q`.
* `jacksonCertNum_shift` — the companion identity driving the bracket.
* `jackson_certificate_closed_form` — the closed form of the left-hand side.
* `jackson_prefactor_closed_form`, `jackson_bracket_closed_form` — the two right-hand factors.
* `jackson_rational_certificate` — `qg:lem-jackson-rational-certificate` verbatim.
-/

set_option autoImplicit false
set_option maxRecDepth 8000

namespace Fabius

/-! ### The certificate numerator and its two division-free identities -/

section CertNum

variable {R : Type*} [CommRing R]

/-- The degree-11 numerator `Q(A; B, C, D, E, F)` driving Jackson's rational certificate.
Writing `eₖ` for the elementary symmetric polynomials of `B, C, D, E, F`,

`Q = A⁶ + A⁵(1 - e₁) + A⁴(e₃ - e₄) + A³(e₁e₅ - e₄) + A²e₅(e₁ - e₂) + Ae₅(e₄ - e₅) - e₅²`.

It has 54 monomials and is symmetric in `B, C, D, E, F`, since every coefficient is a polynomial
in the `eₖ`.  The elementary symmetric polynomials are written out rather than abbreviated by
`let` binders, so that `simp only [jacksonCertNum]` leaves a term `ring` can normalize directly. -/
def jacksonCertNum (A B C D E F : R) : R :=
  A ^ 6
    + A ^ 5 * (1 - (B + C + D + E + F))
    + A ^ 4 * ((B * C * D + B * C * E + B * C * F + B * D * E + B * D * F + B * E * F
          + C * D * E + C * D * F + C * E * F + D * E * F)
        - (B * C * D * E + B * C * D * F + B * C * E * F + B * D * E * F + C * D * E * F))
    + A ^ 3 * ((B + C + D + E + F) * (B * C * D * E * F)
        - (B * C * D * E + B * C * D * F + B * C * E * F + B * D * E * F + C * D * E * F))
    + A ^ 2 * (B * C * D * E * F) * ((B + C + D + E + F)
        - (B * C + B * D + B * E + B * F + C * D + C * E + C * F + D * E + D * F + E * F))
    + A * (B * C * D * E * F) * ((B * C * D * E + B * C * D * F + B * C * E * F
          + B * D * E * F + C * D * E * F) - B * C * D * E * F)
    - (B * C * D * E * F) ^ 2

/-- The first division-free core of Jackson's certificate: after the denominators of the
left-hand side of `qg:eq:jackson-rational` are cleared, the resulting numerator is `1 - A` times
`jacksonCertNum`.  A polynomial identity of total degree 12 whose normal form has 84 monomials,
valid over an arbitrary commutative ring. -/
theorem jacksonCertNum_left (A B C D E F : R) :
    (B - A) * (C - A) * (D - A) * (E - A) * (F - A) * (A ^ 2 - B * C * D * E * F)
        - A ^ 2 * ((1 - B) * (1 - C) * (1 - D) * (1 - E) * (1 - F)
          * (B * C * D * E * F - A ^ 3))
      = (1 - A) * jacksonCertNum A B C D E F := by
  simp only [jacksonCertNum]
  ring

/-- The second division-free core of Jackson's certificate: after the denominators of the bracket
on the right-hand side of `qg:eq:jackson-rational` are cleared, the resulting numerator is
`D (BCD²EF - A³)` times the *same* `jacksonCertNum`.  A polynomial identity of total degree 18
whose normal form has 84 monomials, valid over an arbitrary commutative ring. -/
theorem jacksonCertNum_shift (A B C D E F : R) :
    (D - 1) * (D - A) * (B * C * D * E - A ^ 2) * (B * C * D * F - A ^ 2)
        * (B * D * E * F - A ^ 2) * (C * D * E * F - A ^ 2)
      - (B * D - A) * (C * D - A) * (D * E - A) * (D * F - A)
          * (B * C * D * E * F - A ^ 2) * (B * C * D * E * F - A ^ 3)
      = D * (B * C * D ^ 2 * E * F - A ^ 3) * jacksonCertNum A B C D E F := by
  simp only [jacksonCertNum]
  ring

end CertNum

/-! ### Quotient bookkeeping -/

section FieldLayer

variable {K : Type*} [Field K]

/-- Auxiliary quotient lemma.  If a numerator `n` and a denominator `d` clear by the *same*
nonzero factor `m`, say `n = nc / m` and `d = dc / m` with `dc ≠ 0`, then `1 - n / d` is
`(dc - nc) / dc`.  Both `1 - …` steps of the certificate are of this shape. -/
private theorem one_sub_div_div_of_common_denom {n d nc dc m p : K} (hm : m ≠ 0) (hdc : dc ≠ 0)
    (hn : n = nc / m) (hd : d = dc / m) (hp : dc - nc = p) :
    1 - n / d = p / dc := by
  subst hn
  subst hd
  rw [div_div_div_comm, div_self hm, div_one, one_sub_div hdc, hp]

/-- Auxiliary quotient lemma.  If a numerator clears by `m * v` and a denominator clears by `m`,
then the surplus factor `v` migrates into the denominator of the quotient.  No hypothesis on
`dc` or `v` is needed: if either vanishes, both sides are `0` by the junk-value convention. -/
private theorem div_div_of_common_denom {n d nc dc m v : K} (hm : m ≠ 0)
    (hn : n = nc / (m * v)) (hd : d = dc / m) :
    n / d = nc / (v * dc) := by
  subst hn
  subst hd
  rw [div_div_div_comm, mul_comm m v, mul_div_assoc, div_self hm, mul_one, div_div,
    mul_comm dc v]

/-- Auxiliary quotient lemma: the final cancellation of Jackson's certificate, with every block
abstracted to an opaque atom.  The prefactor's `p` (the four quartic factors), its `d` and its
`m` all cancel against the bracket, and the two sign flips `1 - d = -(d - 1)` and `w' = -w`
compose to `+1`.  This is the whole content of the source's closing cancellation. -/
private theorem jackson_assemble (a q : K) {b c d w w' x y z p m : K} (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (hd1 : d - 1 ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0)
    (hww : w' = -w) (hp : p ≠ 0) (hm : m ≠ 0) :
    a * q / (b * c * x * y * z * w)
      = a * (1 - d) * p / (d * (b * c * y * z * w' * m))
        * (d * m * q / ((d - 1) * x * p)) := by
  subst hww
  have hnw : (-w) ≠ 0 := by
    intro h
    exact hw (by linear_combination -h)
  have h1 : b * c * x * y * z * w ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hb hc) hx) hy) hz) hw
  have h2 : d * (b * c * y * z * (-w) * m) * ((d - 1) * x * p) ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero hd
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hb hc) hy) hz) hnw) hm))
      (mul_ne_zero (mul_ne_zero hd1 hx) hp)
  rw [div_mul_div_comm, div_eq_div_iff h1 h2]
  ring

/-! ### The three closed forms -/

/-- **Closed form of the left-hand side of Jackson's certificate.**  The left-hand side of
`qg:eq:jackson-rational` equals `(1 - A) Q / ((B-A)(C-A)(D-A)(E-A)(F-A)(A² - BCDEF))`, with `Q`
the polynomial `jacksonCertNum`.

This is strictly stronger than the corresponding half of the source lemma: it uses only twelve
of the eighteen definedness hypotheses, omitting `D ≠ 1`, `BCD²EF ≠ A³` and the four conditions
`BCDE, BCDF, BDEF, CDEF ≠ A²` at which the source's right-hand side degenerates to `0/0`. -/
theorem jackson_certificate_closed_form {A B C D E F : K} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hD : D ≠ 0) (hE : E ≠ 0) (hF : F ≠ 0) (hBA : B - A ≠ 0) (hCA : C - A ≠ 0)
    (hDA : D - A ≠ 0) (hEA : E - A ≠ 0) (hFA : F - A ≠ 0)
    (hPr : A ^ 2 - B * C * D * E * F ≠ 0) :
    1 - ((1 - B) * (1 - C) * (1 - D) * (1 - E) * (1 - F)
          * (1 - A ^ 3 / (B * C * D * E * F)))
        / ((1 - A / B) * (1 - A / C) * (1 - A / D) * (1 - A / E) * (1 - A / F)
          * (1 - B * C * D * E * F / A ^ 2))
      = (1 - A) * jacksonCertNum A B C D E F
        / ((B - A) * (C - A) * (D - A) * (E - A) * (F - A)
          * (A ^ 2 - B * C * D * E * F)) := by
  have he5 : B * C * D * E * F ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hB hC) hD) hE) hF
  have hA2 : A ^ 2 ≠ 0 := pow_ne_zero 2 hA
  have hm : B * C * D * E * F * A ^ 2 ≠ 0 := mul_ne_zero he5 hA2
  have hdc : (B - A) * (C - A) * (D - A) * (E - A) * (F - A)
      * (A ^ 2 - B * C * D * E * F) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hBA hCA) hDA) hEA) hFA) hPr
  have hn : (1 - B) * (1 - C) * (1 - D) * (1 - E) * (1 - F)
        * (1 - A ^ 3 / (B * C * D * E * F))
      = A ^ 2 * ((1 - B) * (1 - C) * (1 - D) * (1 - E) * (1 - F)
          * (B * C * D * E * F - A ^ 3)) / (B * C * D * E * F * A ^ 2) := by
    field_simp
    try ring
  have hd : (1 - A / B) * (1 - A / C) * (1 - A / D) * (1 - A / E) * (1 - A / F)
        * (1 - B * C * D * E * F / A ^ 2)
      = (B - A) * (C - A) * (D - A) * (E - A) * (F - A) * (A ^ 2 - B * C * D * E * F)
        / (B * C * D * E * F * A ^ 2) := by
    field_simp
    try ring
  have hp : (B - A) * (C - A) * (D - A) * (E - A) * (F - A) * (A ^ 2 - B * C * D * E * F)
      - A ^ 2 * ((1 - B) * (1 - C) * (1 - D) * (1 - E) * (1 - F)
          * (B * C * D * E * F - A ^ 3))
      = (1 - A) * jacksonCertNum A B C D E F := by
    linear_combination jacksonCertNum_left A B C D E F
  exact one_sub_div_div_of_common_denom hm hdc hn hd hp

/-- **Closed form of the bracket** on the right-hand side of `qg:eq:jackson-rational`.  Its
numerator and its denominator clear by the same monomial `B³C³D⁶E³F³`, so by
`jacksonCertNum_shift` the bracket equals
`D (BCD²EF - A³) Q / ((D-1)(D-A)(BCDE-A²)(BCDF-A²)(BDEF-A²)(CDEF-A²))`.

Note that the last factor of the bracket's numerator has denominator `BCDEF`, not `BCD²EF`; it
reads like a typo in the source but is correct as printed.  No hypothesis `A ≠ 0` is required. -/
theorem jackson_bracket_closed_form {A B C D E F : K} (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hE : E ≠ 0) (hF : F ≠ 0) (hD1 : D - 1 ≠ 0) (hDA : D - A ≠ 0)
    (h4a : B * C * D * E - A ^ 2 ≠ 0) (h4b : B * C * D * F - A ^ 2 ≠ 0)
    (h4c : B * D * E * F - A ^ 2 ≠ 0) (h4d : C * D * E * F - A ^ 2 ≠ 0) :
    1 - ((1 - A / (B * D)) * (1 - A / (C * D)) * (1 - A / (D * E)) * (1 - A / (D * F))
          * (1 - A ^ 2 / (B * C * D * E * F)) * (1 - A ^ 3 / (B * C * D * E * F)))
        / ((1 - 1 / D) * (1 - A / D) * (1 - A ^ 2 / (B * C * D * E))
          * (1 - A ^ 2 / (B * C * D * F)) * (1 - A ^ 2 / (B * D * E * F))
          * (1 - A ^ 2 / (C * D * E * F)))
      = D * (B * C * D ^ 2 * E * F - A ^ 3) * jacksonCertNum A B C D E F
        / ((D - 1) * (D - A) * ((B * C * D * E - A ^ 2) * (B * C * D * F - A ^ 2)
          * (B * D * E * F - A ^ 2) * (C * D * E * F - A ^ 2))) := by
  have hm : B ^ 3 * C ^ 3 * D ^ 6 * E ^ 3 * F ^ 3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hB) (pow_ne_zero 3 hC))
      (pow_ne_zero 6 hD)) (pow_ne_zero 3 hE)) (pow_ne_zero 3 hF)
  have hdc : (D - 1) * (D - A) * ((B * C * D * E - A ^ 2) * (B * C * D * F - A ^ 2)
      * (B * D * E * F - A ^ 2) * (C * D * E * F - A ^ 2)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hD1 hDA)
      (mul_ne_zero (mul_ne_zero (mul_ne_zero h4a h4b) h4c) h4d)
  have hn : (1 - A / (B * D)) * (1 - A / (C * D)) * (1 - A / (D * E)) * (1 - A / (D * F))
        * (1 - A ^ 2 / (B * C * D * E * F)) * (1 - A ^ 3 / (B * C * D * E * F))
      = (B * D - A) * (C * D - A) * (D * E - A) * (D * F - A)
          * (B * C * D * E * F - A ^ 2) * (B * C * D * E * F - A ^ 3)
        / (B ^ 3 * C ^ 3 * D ^ 6 * E ^ 3 * F ^ 3) := by
    field_simp
    try ring
  have hd : (1 - 1 / D) * (1 - A / D) * (1 - A ^ 2 / (B * C * D * E))
        * (1 - A ^ 2 / (B * C * D * F)) * (1 - A ^ 2 / (B * D * E * F))
        * (1 - A ^ 2 / (C * D * E * F))
      = (D - 1) * (D - A) * ((B * C * D * E - A ^ 2) * (B * C * D * F - A ^ 2)
          * (B * D * E * F - A ^ 2) * (C * D * E * F - A ^ 2))
        / (B ^ 3 * C ^ 3 * D ^ 6 * E ^ 3 * F ^ 3) := by
    field_simp
    try ring
  have hp : (D - 1) * (D - A) * ((B * C * D * E - A ^ 2) * (B * C * D * F - A ^ 2)
        * (B * D * E * F - A ^ 2) * (C * D * E * F - A ^ 2))
      - (B * D - A) * (C * D - A) * (D * E - A) * (D * F - A)
          * (B * C * D * E * F - A ^ 2) * (B * C * D * E * F - A ^ 3)
      = D * (B * C * D ^ 2 * E * F - A ^ 3) * jacksonCertNum A B C D E F := by
    linear_combination jacksonCertNum_shift A B C D E F
  exact one_sub_div_div_of_common_denom hm hdc hn hd hp

/-- **Closed form of the prefactor** on the right-hand side of `qg:eq:jackson-rational`.  Pure
monomial bookkeeping: the numerator clears by `B³C³D⁴E³F³` and the denominator by `B³C³D³E³F³`,
which leaves a single surplus factor `D` in the denominator.  `jacksonCertNum` plays no role.

Note that the printed denominator genuinely omits the factor `1 - A/D`: only `B, C, E, F` occur.
Only the five hypotheses `B, C, D, E, F ≠ 0` are needed — at each of the remaining loci of the
source's definedness condition both sides degenerate to `0`, in the same way. -/
theorem jackson_prefactor_closed_form {A B C D E F : K} (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hE : E ≠ 0) (hF : F ≠ 0) :
    (1 - A) * (1 - D) * (1 - A ^ 2 / (B * C * D * E)) * (1 - A ^ 2 / (B * C * D * F))
        * (1 - A ^ 2 / (B * D * E * F)) * (1 - A ^ 2 / (C * D * E * F))
      / ((1 - A / B) * (1 - A / C) * (1 - A / E) * (1 - A / F)
        * (1 - A ^ 2 / (B * C * D * E * F)) * (1 - A ^ 3 / (B * C * D ^ 2 * E * F)))
      = (1 - A) * (1 - D) * ((B * C * D * E - A ^ 2) * (B * C * D * F - A ^ 2)
          * (B * D * E * F - A ^ 2) * (C * D * E * F - A ^ 2))
        / (D * ((B - A) * (C - A) * (E - A) * (F - A) * (B * C * D * E * F - A ^ 2)
          * (B * C * D ^ 2 * E * F - A ^ 3))) := by
  have hmd : B ^ 3 * C ^ 3 * D ^ 3 * E ^ 3 * F ^ 3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hB) (pow_ne_zero 3 hC))
      (pow_ne_zero 3 hD)) (pow_ne_zero 3 hE)) (pow_ne_zero 3 hF)
  have hn : (1 - A) * (1 - D) * (1 - A ^ 2 / (B * C * D * E)) * (1 - A ^ 2 / (B * C * D * F))
        * (1 - A ^ 2 / (B * D * E * F)) * (1 - A ^ 2 / (C * D * E * F))
      = (1 - A) * (1 - D) * ((B * C * D * E - A ^ 2) * (B * C * D * F - A ^ 2)
          * (B * D * E * F - A ^ 2) * (C * D * E * F - A ^ 2))
        / (B ^ 3 * C ^ 3 * D ^ 3 * E ^ 3 * F ^ 3 * D) := by
    field_simp
    try ring
  have hd : (1 - A / B) * (1 - A / C) * (1 - A / E) * (1 - A / F)
        * (1 - A ^ 2 / (B * C * D * E * F)) * (1 - A ^ 3 / (B * C * D ^ 2 * E * F))
      = (B - A) * (C - A) * (E - A) * (F - A) * (B * C * D * E * F - A ^ 2)
          * (B * C * D ^ 2 * E * F - A ^ 3)
        / (B ^ 3 * C ^ 3 * D ^ 3 * E ^ 3 * F ^ 3) := by
    field_simp
    try ring
  exact div_div_of_common_denom hmd hn hd

/-! ### Jackson's six-variable rational certificate -/

/-- **Jackson's six-variable rational certificate** (`qg:lem-jackson-rational-certificate`,
equation `qg:eq:jackson-rational`), transcribed factor by factor.

The hypotheses are exactly the source's "all rational expressions displayed are defined", made
explicit: the six variables are nonzero, and each of the twelve displayed denominator factors is
nonzero.  Two features of the printed formula that read like typos are correct as printed: the
right-hand prefactor denominator omits `1 - A/D` (only `B, C, E, F` occur), and the bracket's
last numerator factor has denominator `BCDEF`, the same as the factor before it.

The proof routes through the common closed form
`(1 - A) Q / ((B-A)(C-A)(D-A)(E-A)(F-A)(A² - BCDEF))` rather than through the source's seed
transformation; see the module docstring. -/
theorem jackson_rational_certificate {A B C D E F : K} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hD : D ≠ 0) (hE : E ≠ 0) (hF : F ≠ 0) (hBA : B - A ≠ 0) (hCA : C - A ≠ 0)
    (hDA : D - A ≠ 0) (hEA : E - A ≠ 0) (hFA : F - A ≠ 0)
    (hPr : A ^ 2 - B * C * D * E * F ≠ 0) (hD1 : D - 1 ≠ 0)
    (hM : B * C * D ^ 2 * E * F - A ^ 3 ≠ 0) (h4a : B * C * D * E - A ^ 2 ≠ 0)
    (h4b : B * C * D * F - A ^ 2 ≠ 0) (h4c : B * D * E * F - A ^ 2 ≠ 0)
    (h4d : C * D * E * F - A ^ 2 ≠ 0) :
    1 - ((1 - B) * (1 - C) * (1 - D) * (1 - E) * (1 - F)
          * (1 - A ^ 3 / (B * C * D * E * F)))
        / ((1 - A / B) * (1 - A / C) * (1 - A / D) * (1 - A / E) * (1 - A / F)
          * (1 - B * C * D * E * F / A ^ 2))
      = (1 - A) * (1 - D) * (1 - A ^ 2 / (B * C * D * E)) * (1 - A ^ 2 / (B * C * D * F))
            * (1 - A ^ 2 / (B * D * E * F)) * (1 - A ^ 2 / (C * D * E * F))
          / ((1 - A / B) * (1 - A / C) * (1 - A / E) * (1 - A / F)
            * (1 - A ^ 2 / (B * C * D * E * F)) * (1 - A ^ 3 / (B * C * D ^ 2 * E * F)))
        * (1 - ((1 - A / (B * D)) * (1 - A / (C * D)) * (1 - A / (D * E))
              * (1 - A / (D * F)) * (1 - A ^ 2 / (B * C * D * E * F))
              * (1 - A ^ 3 / (B * C * D * E * F)))
            / ((1 - 1 / D) * (1 - A / D) * (1 - A ^ 2 / (B * C * D * E))
              * (1 - A ^ 2 / (B * C * D * F)) * (1 - A ^ 2 / (B * D * E * F))
              * (1 - A ^ 2 / (C * D * E * F)))) := by
  have hP4 : (B * C * D * E - A ^ 2) * (B * C * D * F - A ^ 2) * (B * D * E * F - A ^ 2)
      * (C * D * E * F - A ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h4a h4b) h4c) h4d
  have hww : B * C * D * E * F - A ^ 2 = -(A ^ 2 - B * C * D * E * F) := by ring
  rw [jackson_certificate_closed_form hA hB hC hD hE hF hBA hCA hDA hEA hFA hPr,
    jackson_prefactor_closed_form (A := A) hB hC hD hE hF,
    jackson_bracket_closed_form hB hC hD hE hF hD1 hDA h4a h4b h4c h4d]
  exact jackson_assemble (1 - A) (jacksonCertNum A B C D E F) hBA hCA hD hD1 hDA hEA hFA hPr
    hww hP4 hM

end FieldLayer

end Fabius
