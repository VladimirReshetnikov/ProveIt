# Three fewer unrestricted integer variables at degrees four, six, and eight

Source repository: `VladimirReshetnikov/ProveIt`.
Source snapshot: `ae3007ca4467011e0e051c84acb4a1dd13971b0e`.

This note combines two distinct delivered wave-3 results. Package 20 supplies
low-degree polynomial lifts over unrestricted integers. Package 23 proves
that the half-binomial scale may be required merely to be odd: the arithmetic
equations force it to be positive, and accepting computations have odd scale.
Applying that theorem to the existing low-degree lifts removes three guard
parameters without increasing degree.

## 1. Exact new assertions

The generated JSON packets give every residual as an expanded integer
polynomial. Fixed numeral ports are bound to one complete coefficient tuple.
For each packet, define its single polynomial to be the sum of the squares
of all listed residuals. The three resulting polynomials have the following
sizes.

| Polynomial | Unrestricted integer unknowns | Residual equations | Maximum residual degree | Single polynomial degree |
|---|---:|---:|---:|---:|
| Q51 | 51 | 30 | 2 | 4 |
| Q42 | 42 | 21 | 3 | 6 |
| Q36 | 36 | 15 | 4 | 8 |

In each case ZFC proves

    no integer zero of Qn  <=>  Con(ZFC).

The assertion uses the same syntactic ZFC proof predicate as the existing
K215 endpoint. It is an ordinary mathematical composition of the stated
Pell/compiler theorems. No new Lean or Rocq theorem is asserted.

The corresponding source counts in package 20 are 54, 45, and 39 integer
unknowns. The new construction strictly reduces each of those counts by three
at exactly the same single-polynomial degree. This is a comparison with the
listed constructions, not a universal minimality claim.

## 2. The substitution and the complete polynomials

In each source packet the half-binomial scale `s` is retained as an independent
integer coordinate. Positivity is imposed by the separate residual

    s - 1 - s_pos1^2 - s_pos2^2 - s_pos3(s_pos3+1).

Delete that residual and its three parameters. Replace the coordinate `s`
everywhere else by

    s = 2 v_scale + 1,

where `v_scale` is one unrestricted integer coordinate replacing `s`. This
is an oddness restriction, not a polynomial identity equivalent to the old
guard on all tuples. Soundness and completeness of the new existential
predicate are proved below; they do not follow merely by removing a guard.

The generator checks that the three deleted guard parameters occur nowhere
else. Its outputs are:

* `generated/integer51_degree4_odd_scale.json`;
* `generated/integer42_degree6_odd_scale.json`;
* `generated/integer36_degree8_odd_scale.json`.

Each output contains the full variable list, fixed-numeral binding, source
hash, every expanded residual, and an exact leading-degree certificate.
Thus no universal Diophantine index or unspecified existence theorem is
being substituted for an explicit polynomial description.

## 3. Fixed coefficient tuple

Use the entire compact tuple from package 19:

    wang943-compact-5pow10.

Its four ports are beta=B-1, K, MC, and shifted MF_source=MF_native+B-1,
with B=2^(5^10). The full finite recipe and compiler proof are included in
`upstream/19-wang943/compiler/WANG943_COEFFICIENTS.md` and
`WANG943_COMPACT_LAYOUT.md`. The complete manifest is
`upstream/19-wang943/COEFFICIENT_BINDING.json`; all four exact coefficient
payloads are included as deterministic `.bin.gz` files. They decompress to
unsigned little-endian integers, 5,312,269 bytes in total. The four payloads
are 20,260 compressed bytes in total. Their hashes are copied into each
generated packet so the selected instance is unambiguous.

The unchanged parent polynomial packets still record package 20's historical
4094-tile binding. They are preserved as source provenance. The new outputs
replace that entire tuple, using the explicit arithmetic interface proved
by package 19. No single port is replaced independently.

Package 19's compact proof, Section 2.5, establishes

    MC = 2 (mod 4),       MF_native = 4 (mod 8),
    popcount(MC)+popcount(MF_native)=d,       d=5^10,

and retains the inputless compiler interface, no-carry and strict raw-slack
bounds, actual-rank tuning, and canonical completeness. Its original language
proof explicitly permits arbitrarily large independently chosen five-power
tableau widths and heights. Thus the tableau area N is odd and the canonical
dyadic exponent t=dN is odd. The marked Start and masks give

    C=1 (mod 4), q=0 (mod 4), J=1 (mod 4),

and the exact shifted packing gives `R=3 (mod 4)` and `R>t` as in the common
compiler proof. If `S=(C-1)+qF` and
`Tmask=(MC J+1)+q(MF_native J-1)`, the native disjoint-mask condition and
balanced populations yield

    popcount(Tmask)=t+2,
    R=(q^2-1-S)q^2+(S+Tmask),
    popcount(R)=2t+popcount(Tmask)=3t+2.

Consequently the canonical half-binomial scale is odd. Also
`w=2^(R-t)` is a square because R and t are odd. In the auxiliary Pell
construction, the usual choice of rank m=cR makes
`psi_A(m)/c^2` odd; the normalized multiplier is that quotient and the
ordinary multiplier is its product with the odd Delta. This proves the
odd-i/square-w/odd-s properties needed here for the complete 943-tile tuple.
The argument uses exactly the same explicit identities as packages 20 and 23,
whose hypotheses have just been checked. No unproved stronger compiler
contract is introduced by the tuple transfer.

## 4. The odd-scale theorem used here

Package 23's `ODD_SCALE_27_PROOF.md`, included unchanged under `upstream/`,
establishes the following statement for the common ordinary or normalized
Pell/compiler interface. Guard only

    J,F,alpha,z,eta,zeta > 0,

put `i=2r+1`, `s=2v+1`, `w=u^2`, and let the remaining coordinates range
over the integers. Then the arithmetic system has a solution if and only
if the authentic blank K215 computation halts.

The proof is not based on testing negative values. It assumes `s<0`, writes
`Z=-Y`, `B=-(a+2)`, and `c0=-c`, recovers the positive main Pell rank `p=R`,
and proves `Z>2^R`. For the two possible signs of the main root the defining
congruence then gives respectively

    X = -2^R (mod H),   or   X*2^R = 1 (mod H).

Both are contradicted by the explicit bounds in the proof. Thus every
solution has `s>0`. Canonical accepting witnesses have

    v_2(Y)=popcount(R)-2=3t,

so `Y=sq^3` forces positive odd `s` and hence an integer
`v_scale=(s-1)/2`. These are the soundness and completeness facts required
for deleting the three positivity parameters.

## 5. Sextic and octic soundness

The sextic and octic parents were obtained by exact polynomial elimination
of registers from, respectively, the normalized and ordinary signed
Pell/compiler systems. Package 20's source proof explicitly establishes
that these eliminations are identities for arbitrary integer tuples. The
sextic first-root shear is an affine bijection of its unrestricted integer
coordinate. It does not require a sign for the sheared coordinate.

Take a common zero of the new sextic or octic residuals. Restore all the
eliminated registers by the displayed source identities. The six unchanged
guard constraints force exactly `J,F,alpha,z,eta,zeta>0`; the odd auxiliary
multiplier and square power scale constraints are unchanged. The new scale
is odd. This is precisely a solution of the signed interface in Section 4.
That theorem proves `s>0` and decodes a blank K215 halt. Thus every integer
zero of Q42 or Q36 gives a finite syntactic ZFC refutation.

## 6. Quartic soundness and the exposed-quotient point

The quartic parent retains two quotient variables `o,j` instead of the
single quotient `T`. A gap would arise if one invoked a source theorem
requiring `T` before proving that an integer `T` can be recovered. There are
two valid routes; the direct congruence route is shortest.

The quartic equations restore the common definitions

    q=beta J+1, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y,
    H=4a+3, Delta=a^2+H, D=X+ac+gamma H,

and the exposed identities

    V=of-c,       V=jc-R.

Consequently they give the two integer congruences

    V=-c (mod |f|),       V=-R (mod |c|),

as soon as the nonzero moduli have been established. Package 23's
negative-scale proof uses the eliminated-quotient formula only to obtain
these two congruences. Its other hypotheses and all the Pell equations are
present verbatim in the quartic projection. In particular `s` odd implies
`Y` nonzero; the main congruence excludes `w=0`; and, under `s<0`, the proof
gets `c0=-c>0` and a nonzero `f` from the ordinary strong equation. The
negative-scale proof therefore applies directly with the displayed
congruences, without making any assumption about the signs of `o` or `j`.
It excludes `s<0`. Since `s` is odd, this proves `s>0`.

Now package 20's positive-scale signed proof applies in its original order.
The ordinary strong-rank lemma gives `f^2=1 (mod c)`. Since

    of+R=(j+1)c,

one has

    o+Rf = f(of+R)-o(f^2-1) = 0 (mod c).

Thus `T=(o+Rf)/c` is an integer and

    c(Tf-1)-Rf^2=of-c=V.

This recovers the ordinary signed interface and hence a blank K215 halt.
The proof never infers integrality by dividing an unchecked congruence.

Equivalently, in the negative-scale branch one may apply the ordinary
strong-rank lemma from package 23 first, with `c0=-c`, recover the same
congruence `f^2=1 (mod c0)`, and then construct `T` by the preceding identity.
That gives the same contradiction with the negative-scale theorem. Both
orders establish the divisibility before using the quotient.

## 7. Completeness for all three forms

Assume K215 halts on the blank tape. Use the authentic canonical witnesses
for package 19's selected compiler tuple. Its five-power padding and exact
population identity are retained, so Section 4 supplies positive odd `s`.
Choose `v_scale=(s-1)/2`. The other six positive guards admit the usual
three-variable positive representations

    Pos(x,y,z)=1+x^2+y^2+z(z+1),

and the already established odd auxiliary multiplier and square `w` remain
valid. Assign the lift registers and, for the quartic, the exposed `o,j`
exactly as in the original low-degree proof. Every new residual vanishes.
Therefore each new system has an unrestricted integer solution.

This proves solvability equivalence in both directions. The sum-of-squares
step is valid over the integers, since a finite sum of squares is zero
exactly when every squared integer is zero. Composing with the established
K215/refutation calibration yields the stated ZFC-provable equivalences.

## 8. Exact degree and size certificates

The substitution `s=2v_scale+1` is affine, so it cannot increase any residual
degree. Deleting the quadratic positivity residual likewise cannot increase
degree. To prove that the degrees do not fall, use these coefficients in
the fully expanded sum of squares:

    [tau^4] Q51 = 1,
    [Jrep^2 L^2 v_scale^2] Q42 = 4 beta^2,
    [Jrep^6 v_scale^2] Q36 = 4 beta^6.

The fixed beta is strictly positive. These coefficients are therefore
nonzero on the authentic compiler tuple. The exact degrees are 4, 6, and 8.
The generator computes them over a symbolic polynomial ring rather than
specializing the coefficients to small diagnostic integers.

Three independent guard parameters disappear from each variable list, and
one residual disappears from each list of equations. Replacing `s` by
`v_scale` is a rename of a single coordinate. Thus the exact counts are

    (54,31) -> (51,30),
    (45,22) -> (42,21),
    (39,16) -> (36,15).

The generated sparse sum-of-squares term counts, with the fixed ports kept
symbolic, are respectively 342, 467, and 845. These are description counts;
they are not bounds on expanded integer coefficient height.

## 9. Reproduction and evidence boundary

Run `python3 build_odd_scale_lifts.py`. It requires only Python's standard
library and the included exact polynomial utility from package 20. It checks
the unique deleted guard, absence of its parameters elsewhere, exact affine
substitution, variable liveness, all residual degrees, sum-of-squares degree,
and the explicit nonzero-degree certificates. Small signed evaluations are
additional transcription diagnostics only.

The inherited semantic proofs are not certified by these finite checks. The
proof of solvability equivalence is Sections 4-7, using the specified source
Pell/compiler statements. No halting computation or consistency assertion
is assumed or discovered by the program.

## 10. Attribution and further work

The base lifts and polynomial utility are from wave-3 package 20. The exact
compact 943-tile tuple and its compiler adapter are from wave-3 package 19. The
odd-scale theorem is from wave-3 package 23.
The contribution here is their explicit composition, including the
exposed-quotient audit, exact 51/42/36-variable polynomials, and exact
uniform degree certificates. This is AI-assisted research intended for
integration in ProveIt.

Natural next questions are whether another retained positivity guard is
forced by parity and the arithmetic equations, whether the sextic and
octic register eliminations can be optimized after the odd-scale change,
and whether a formal proof can cover these affine substitutions and the
exposed-quotient extension as reusable lemmas.
