# Independent mathematical audit of the four-root, fourteen-integer construction

This is an internal independent proof review, not external peer review or a
proof-assistant certificate. The statements here concern the proposed algebraic
and arithmetic reduction; the native compiler/refutation calibration remains
the identified inherited ordinary theorem.

## 1. Modular separation uses rational arithmetic only

Let `a_1,...,a_m` be nonzero rational numbers with denominators not divisible by
3, all nonzero modulo 3, and let nonzero rational weights `w_i` have pairwise
distinct integer 3-adic valuations. For arbitrary choices of square roots in
an algebraic closure of the rationals, no nonempty signed subset of
`w_i sqrt(a_i)` sums to zero.

Here the valuation refers only to rational numbers. There is no need to extend
it to a number field. For a proposed zero subset, divide by the rational power
of 3 of its least weight valuation, and incorporate the weights into the
radicands. The resulting radicands `b_i` have one 3-adic unit `b_1`, while every
other `b_i` is divisible by 9 in the localization `Z_(3)`. If the subset has at
least two members, form

```
F = product over all signs epsilon_2,...,epsilon_m
      (sqrt(b_1) + sum epsilon_i sqrt(b_i)).
```

Each sign reversal of a radical permutes the factors, including reversal of
the first radical because there are an even number of factors. Thus `F` is an
integer-coefficient polynomial in the `b_i`. Modulo 3 it is
`b_1^(2^(m-2))`, which is nonzero. A vanishing signed subset would make one
factor zero, a contradiction. A singleton cannot vanish because its radicand
and weight are nonzero.

If a weighted sum of these roots is rational, its finite multiquadratic
splitting field is a Galois extension of Q. Every automorphism that changes
one or more root signs would give, by subtracting the unchanged rational sum,
a forbidden nonempty signed zero subset. Consequently every root is fixed by
the Galois group and hence rational. This proof applies to complex roots too;
positivity of every radicand need not be proved in advance.

## 2. Congruences of the proposed literal interface

Take the coherent source-34 beta, so `beta=2^1064921-1` is odd and is 1 modulo
3. Put `J=6j+1`, `q=beta*J+1`, `W=4(3w+1)`, `X=qW`, and
`Y=(2v+1)q^3`. Then q and Y are even, q and X are 2 modulo 3, and W is 1
modulo 3. Hence

```
a=(X+1)Y is even and divisible by 3,
H=4a+3 is odd, nonzero and divisible by 3,
Delta=a^2+H is odd and divisible by 3.
```

For `u=E Y k=XY^2 k`, put `b=XY^2`. Modulo 3, b is either 0 or 2, so
`A=u(u+k)+1=b(b+1)k^2+1` is 1 modulo 3.

With `L=(2r+1)c^2`, `F2=1+Delta L^2`, and `Q=Delta^2 L^2`, the four rational
radicands are

```
F2, A, B=(QV^2-1)/(Q-1), Dm=1+Delta c^2.
```

All are units congruent to 1 modulo 3. Indeed 9 divides Q, so Q-1 is a unit
and B is 1 modulo 3. The weights `9,3,1,1/H` have valuations
`2,1,0,-v_3(H)`, respectively, and these are distinct. The previous lemma
therefore applies to the four-root sum.

The shared positivity guard proves `eta(k-eta)>0`. With eta=c-Yk this gives
`|c|>(|Y|-1)|k|`, and the fixed large beta makes `|c|>1`. Consequently L is
nonzero, Delta is nonzero, and Q>1 before any omitted root is recovered.

## 3. Soundness of the normalization and the squared-modulus CRT

Rationality from the four-root norm makes the recovered f, tau and d integers,
since each squares to an integer. The recovered auxiliary y satisfies
`Q V^2-(Q-1)y^2=1`; the inherited adjacent-coefficient Pell descent makes y an
integer because Q>1. For an uncentered sum coordinate

```
xi = 9f + 3tau + y + (d-b0)/H,
```

the integral xi, f, tau and y force `(d-b0)/H` to be an integer gamma. Thus
the old main Pell root is `d=b0+H gamma` with a genuine integer gamma.

Restore the ordinary strong ordinate by `I_old=Delta L`. Then

```
I_old^2 = Delta(f^2-1),
I_old/c^2 = Delta(2r+1),
```

and the latter is odd because Delta is odd. Thus the old odd-scale coordinate
is integral. The chosen auxiliary expression

```
V=f^2(cT-R)-c
```

restores the source quotients by the polynomial formulas

```
o = f(cT-R),
j_old = f^2 T-1-Delta(2r+1)^2 c^3 R.
```

Indeed `V=fo-c=j_old c-R`. This does not assume that every old solution has
o divisible by f: soundness constructs an old solution from a new solution,
and completeness below chooses suitable new canonical witnesses.

## 4. Completeness with the same canonical native family

The source-34 canonical q is a power of 2, its native J is odd and is 1 modulo
3, and its rank R is 3 modulo 4. Therefore J is 1 modulo 6, and the stronger
affine restriction J=6j+1 preserves those canonical witnesses. The main base
`A_base=a+2` is even. With `c=psi_(A_base)(R)`, both c and R are odd.

Choose `m=cR`, `L=psi_(A_base)(m)` and `f=chi_(A_base)(m)`. Pell composition
gives

```
L = c psi_D(c), where D=chi_(A_base)(R).
```

The main Pell identity implies `D^2=1 modulo c`. The polynomial congruence
`psi_D(c)=c D^(c-1) modulo c` then proves c divides psi_D(c), so c squared
divides L. Since the base is even and m odd, L is odd, and L/c squared is
odd as required. Thus `L=(2r+1)c^2` for an integer r.

The Positive auxiliary reconstruction lemma retained in package 61's report
(lines 493-533 of the inspected local copy) applies with this L: it requires
`R>=3`, `R=3 mod4`, `c=psi_(A_base)(R)`, `f^2-Delta L^2=1`, and c dividing L.
It explicitly supplies T and y with

```
V=f^2(cT-R)-c,
Q V^2-(Q-1)y^2=1.
```

This is exactly the stronger squared-modulus progression used in the new
construction. No unproved extra congruence or generic CRT assumption is
needed. The determinant and nearest-square guards depend on the unchanged
native/main coordinates, so their canonical witnesses can be retained.

## 5. Remaining implementation checks

The mathematical reduction above is coherent. Before release, the literal
norm circuit must be checked against its sixteen conjugate factors, and any
centering must preserve the required integrality of gamma and the selected
sum coordinate. Its actual variable count, exact degree and operation count
must be measured from the final circuit, with the entire fixed numeral tuple
kept together. These metrics are not asserted by this review alone.

## 6. Extension to thirteen unrestricted integer coordinates

The subsequent thirteen-variable construction makes `c=2c1+1` syntactic,
deletes the first private positivity coordinate p1, and defines the integer

```
Bguard = det*eta_zeta-(pair_root^2-det-eta_zeta+1)^2
         -1-pair_pos2^2-pair_pos3(pair_pos3+1).
```

The former guard is exactly `G=Bguard-p1^2`. A new quadratic norm adjoins
`w^2=Bguard` and replaces xi in the raw four-root norm by `xi-54w`.

The recovery proof does not use the deleted guard to establish Q>1. Because
a is a multiple of 6, `Delta=(a+1)(a+3)>=3`, and c and `2r+1` are odd nonzero
integers. Thus U is nonzero and `Q=Delta^2 U^2>=9` for every tuple, before
any omitted root is recovered.

The centered four-root weights are now `18,6,2,2/H`, with 3-adic valuations
`2,1,0,-v_3(H)`. The added root `54w` has squared 3-adic valuation at least
6 whenever Bguard is nonzero, and is zero when Bguard is zero. This does not
require Bguard to be positive or a unit. In a signed subset containing at
least one old root, the least valuation is attained by a unique old root;
after normalizing its weight, its radicand is a 3-adic unit and all other
radicands are divisible by 3. The same sign-product argument of Section 1
therefore excludes such a zero subset. In the finite multiquadratic Galois
extension, no automorphism can change an old root while fixing the rational
sum. The four old roots are rational, and the sum identity then makes w
rational. Since `w^2=Bguard` is an integer, w is an integer. Set p1=w to
restore G exactly. A negative Bguard is therefore automatically rejected;
its positivity need not be assumed before root recovery.

The centering used in the compact packet is

```
Z=H[xi+18(a+2)U+3(2u+k)+2V]+2D0.
```

Its five-root identity is

```
xi+18(a+2)U+3(2u+k)+2V+2D0/H
 =18f+6tau+2y+2d/H+54w.
```

After f, tau, y and w have been proved integral, this implies that
`2(d-D0)/H` is an integer. Since H is odd and d-D0 is integral, `(d-D0)/H`
is an integer too, restoring gamma. All previous source restoration maps
then apply. This establishes soundness without a circular appeal to the
guard or to an already recovered main Pell root.

For completeness the native canonical c is odd, as established in Section
4, so c1=(c-1)/2 is integral. Retain its old p1 and replace the centered sum
coordinate by xi+54p1. This produces a new integer zero. No claim that every
old noncanonical solution has odd c is needed: the construction proves an
existence equivalence using the available canonical family.

## 7. Completed finite independent checks

`check_compact_norms.py` now proves the compact three- and four-root norm
identities by exact expansion against all eight and sixteen signed linear
factors. It separately proves every operation of the quadratic-pair algebra
in `Z[e,o,f,p,b,w]/(w^2-b)`. These are polynomial identities, so their
composition proves the thirty-two-factor interpretation of the thirteen-
variable norm without relying on random evaluations.

Independent carry-free integer convolution evaluates each literal circuit
on an exact univariate specialization over the field of 65,521 elements,
using the actual fixed numerals. The complete specialized polynomials agree
with the distinct dense implementation. Their nonzero leading terms are:

| Variables | Specialized polynomial degree | Leading coefficient mod 65521 |
|---:|---:|---:|
| 13 | 1392 | 56423 |
| 14 | 696 | 50632 |
| 15 | 244 | 16359 |
| 16 | 108 | 19526 |

These certify lower bounds; the respective upper bounds come from the exact
norm identities and the separately supplied degree analysis. The literal
live binary operation counts are 205, 151, 137 and 132 in the same order.
The checker also performs 128 modular diagnostics for each compact/dense
pair, explicitly distinct from the universal identity proofs. Its receipt
records the exact circuit hashes inspected.

## 8. Exact primary formula-to-gate correspondence

`check_primary_formula.py` supplies an additional check beyond metadata closure
or compact/dense sampling. It imports neither builder. It independently states
the twenty-eight primary abbreviations, constructs the displayed cleared norm
formula and its final quadratic norm, and compares that expression with the
actual 205 literal gates using exact canonical expression DAGs. The comparison
uses only integer ring identities and succeeds without random evaluation or
numeric specialization. Every retained native abbreviation is additionally
identified inside the actual gate expressions.

The checked scaling is `delta^8` for the four-root norm, and `delta^16` after
the last quadratic norm. Its radicands are `324 H^2 F2`, `36 H^2 A`, `4 Dm`,
and `4 H^2 (QV^2-1)/delta`. The last quadratic root has square
`2916 H^2 Bguard=(54H)^2 Bguard`, so its substitution `Z-w` is exactly the
required replacement `xi -> xi-54p1`, rather than an incorrectly scaled shift.

The same checker compares the entire six-port tuple byte-for-byte with the
inspected source-34 tuple in the pinned Pell-congruence archive, verifies the
binding hashes and the literal beta/cone exponents, and preserves the already
shifted MF convention. Its independent receipt is `PRIMARY_FORMULA_CHECK.json`.
