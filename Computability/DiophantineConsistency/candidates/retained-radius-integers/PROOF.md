# Retaining arithmetic wires lowers the integer coefficient height

Let P be `raw_natural.json`. It retains all 1,259 coordinates and all
1,177 quadratic rows of the frozen
`projected-factorial-radius/both_source/raw_builder.json`. In particular,
the small coefficients are obtained by retaining intermediate arithmetic
wires, not by scaling an equation or discarding a condition. Its expanded
sum of squares has 3,877 terms and actual coefficient height 427.

Every equation below has unrestricted integer variables. All source,
factorial, power, CRT and proof-calculus semantics are inherited from the
unchanged natural parent. The changes proved here concern exact algebra
and domain conversion only.

## 1. Complete raw-source binding

Every variable and polynomial row of P is compared with the frozen raw
builder. The separately pinned raw-export checker then reconstructs the
complete frozen 667-natural-coordinate, 585-row source. It verifies all
1,029 raw gate definitions, including the 17 signed-difference-square
identities, and all 592 omitted affine wires. No free input is omitted.

In the forward direction every natural raw zero satisfies the retained
667-coordinate rows. In reverse, each omitted affine gate is restored in
its topological order by the indicated ordinary addition or multiplication
of already natural values. Each of the 17 signed intermediate differences
is used only through its exact square. Its restoring expression is that
square and therefore is natural. The full polynomial checks identify every
raw row after restoration. Thus existence of a natural zero of P is
equivalent to existence of a natural zero of the frozen source.

No assertion that an arbitrary signed affine expression preserves
nonnegativity is used. The complete affine/square schedule is checked by
`raw_export`, rather than inferred from variable names or an intended
arithmetic interpretation.

## 2. Fresh actual-row signs

A fresh certificate selects 161 coordinates of P as nonnegative seeds.
It derives the other 1,098 signs in a stored order. Each inference uses
an actual polynomial row, possibly multiplied by -1, of the form

```
c*x = F,                 c a positive integer, x absent from F.
```

For 1,081 inferences F has nonnegative coefficients; every variable
occurring to an odd exponent is already certified nonnegative. Even
powers are nonnegative for arbitrary integer values, so F>=0. The other
17 inferences give the full F as an exact affine square. The checker
expands that square and compares it with the entire row. These also
give F>=0 independently of operand signs. Consequently x>=0 in every
case. Induction proves that all 1,259 original coordinates are natural.

This sign proof holds at every integer zero of the actual rows, before
any macro or source theorem is applied. There is no appeal to a candidate
factorial's intended meaning, no sign inferred from a variable's kind,
and no guard set transferred by matching names. The selection heuristic
is not part of the proof. Neither 161 nor a final variable count is claimed
minimal, including within a particular inference rule class.

## 3. Exact private quadratic guards

For each seed x introduce three private integer coordinates a,b,c and
append

```
x-a^2-b^2-c(c+1)=0.                                      (1)
```

For every integer c, c(c+1)>=0; hence (1) forces x>=0.
Conversely, for a natural x the number 4x+1 is not of Legendre's
exceptional form 4^a(8b+7), so it is a sum of three integer squares.
Modulo four precisely one of those squares is odd. Write the squares as
(2c+1)^2,(2a)^2,(2b)^2, subtract one, and divide by four to obtain (1).
Thus each natural seed has guard witnesses, independently and
simultaneously for all seeds.

Retain every row of P and all 161 guards. The augmented integer system Q
has 1,742 coordinates and 1,338 quadratic rows. A zero of Q gives all seed
signs by the guards, then all original signs by Section 2, and therefore
a natural zero of P. Every natural zero of P extends to Q by the private
three-square witnesses. These implications are unbounded.

Guards are appended as quadratic rows; natural coordinates are not
substituted by quadratic expressions inside old rows. Consequently the
sum of squares stays quartic.

## 4. Signed monic projections

At each certified step, a current row is exactly v-f or its negative,
where f is an integer polynomial independent of v. Substitute v=f into
every other row and delete the defining row. A step is allowed only if
every resulting row still has degree at most two. A further row can be
removed only when its whole substituted polynomial is identically zero.

The full restoring polynomial and order are retained. Reversing the order
assigns each removed variable its unique integer value after restoring
the variables on which it depends. Every step is an exact unbounded
integer equivalence: no denominator, sign condition, finite search, or
surjectivity assumption is present. All five certificates have an empty
`unconstrained_removed` list, so no free coordinate is silently forgotten.

Every guard is substituted along with every other row. For soundness,
first restore the entire integer parent Q, including all guard equations;
only then use Sections 2 and 3 to extract a natural zero. Restoring
polynomials may have negative coefficients and values. They are never
assumed to preserve the natural numbers.

## 5. Literal results and verification

Each final equation is the sum of squares of all its listed quadratic
rows. Over the integers it vanishes exactly when all rows vanish. The
independent checker expands the entire sum of squares, compares every
collected integer coefficient, verifies exact degree four and verifies
that every declared variable occurs.

| Integer variables | Quadratic rows | Collected terms | Actual height |
|---:|---:|---:|---:|
| 1,742 | 1,338 | 6,200 | 427 |
| 1,095 | 691 | 5,044 | 4,750 |
| 950 | 546 | 6,808 | 737,653 |
| 886 | 482 | 10,158 | 737,653 |
| 872 | 468 | 10,122 | 938,261 |

The 1,095 point has fewer terms but more coordinates than the 950 point;
the 886 and 872 points trade coordinates against terms or height. A
quadratic-only projection probe had 1,153 coordinates, 749 rows, 5,179
terms and height 4,750, so it is dominated by the supplied 1,095 point
and is not retained. No global simplicity optimum is claimed.

The independent checker imports only pinned algebraic row/sign,
projection and polynomial verifiers, not a sign selector, optimizer or
producer. It checks the full raw export and all five complete signed
inverse certificates. Three arbitrary off-source signed assignments per
child test every surviving and deleted row. Eight mutation controls
change a restoration, sign row, inference order, guard, or collected
coefficient and must be rejected. These finite controls supplement the
exact identities above; they do not search for a refutation or decide
whether an equation has a zero.

The arithmetic engine is read from the immutable, reviewed 407 archive
with SHA256
`59f847872298260ee35e9d8e4cd0b52d2d78658ac523981fe060e81f40ca4a59`.
The parent and checker source files have complete SHA256 bindings in
`PARENT_PINS.json`. Normal and optimized Python independently rebuild and
verify all literal data. No Lean, historical H10 emitter or native
coefficient generator is run. This establishes no new internal object-ZFC
derivation and does not prove consistency.
