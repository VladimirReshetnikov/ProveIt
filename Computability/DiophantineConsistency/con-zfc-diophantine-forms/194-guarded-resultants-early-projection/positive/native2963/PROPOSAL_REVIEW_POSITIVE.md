# Review of the positive-variable Pell proposals, wave 7

This review examines the arguments behind packages 38, 44, 49, 50, 52,
and the short-equation component of 53. The reviewed wave-7 intake is
commit `6d375f2d2d`; the delivered packages themselves pin their inherited
mathematics to `124c07c0b77a9e20e84676514d8b1ff78536ea3f`.
The original archives were recovered from commit `4b4349064a`, so omitted
duplicate files in the intake tree did not prevent replay.

No new local mathematical obstruction was found in the positive reductions.
The best eleven-positive proposal reviewed here is package 52's degree-954,
113-operation equation. Its twelve-positive degree-897, 108-operation
companion also improves package 44. These remain ordinary mathematical
reductions with inherited native-compiler and Pell dependencies; their finite
auditors do not supply those missing Lean theorems.

## Comparison on the stated domains

Every row below is one equation over strictly positive integers. An operation
is one live binary addition, subtraction, or multiplication, including a
multiplication by a numeral. Systems with free comparisons are separate
comparison points.

| Construction | Variables | Exact degree | Operations | Assessment |
|---|---:|---:|---:|---|
| 38, main carrier | 11 | 1154 | 123 | Improved by 52 |
| 38, translated companion | 11 | 1140 | 129 | Improved by 52 |
| 44, full carrier | 12 | 901 | 112 | Improved by 52 |
| 49, full absorbed carrier | 11 | 990 | 117 | Improved by 52 |
| 49, short absorbed carrier | 11 | 994 | 115 | Improved by 52 |
| 50, midpoint carrier | 11 | 954 | 115 | Same degree as 52, two more operations |
| 52, lean Y-absorption | 11 | 954 | 113 | Best reviewed eleven-positive point |
| 52, unabsorbed lean carrier | 12 | 897 | 108 | Best reviewed twelve-positive point |
| 49, two positive gap substitutions | 15 | 44 | 76 | Degree improvement over local normalized P76 |
| 53, relaxed P72 | 15 | 80 | 72 | Degree/cost tradeoff; saves one operation against P73 |
| 53, relaxed P74 | 15 | 56 | 74 | Historical Q56 point, not a new frontier point |

Historical P67 has degree 155 in 67 operations and remains an explicit
comparison point for the positive-family changes reviewed here. It is no
longer the scalar operation-count record: package 51 supplies a degree-157,
66-operation equation, covered by the parallel review. The historical
degree/cost pairs 99/69, 93/70, and 83/71 also remain relevant. In particular,
the local 111/69 equation does not improve the historical 99/69 point.
Package 47 separately improves
the degree-44 point to 75 operations; its review belongs to the parallel
small-equation audit. None of these observations proves a global minimum.

For comparison with the local Lean work, P75 is degree 68 in 75 operations;
the local reduced-strong P76 is degree 64 in 76 operations. Their checked
same-coordinate equivalences do not by themselves certify the changed
ordinary strong norm in packages 49 and 53. The native compiler equivalence
is also separate from the generic closed nine-variable construction.

## The deleted quotient in package 38

The apparent cancellation hazard in
[the eleven-positive proof](con-zfc-diophantine-forms/38-batching11/eleven/ELEVEN_POSITIVE_PROOF.md)
is handled correctly. Rational radical recovery first proves only
`E | H(k-R-1)`. One cannot cancel `H` at this stage. The subsequent Pell
argument obtains the main rank `p=R` independently, and the first Pell rank
then satisfies `1 <= n < R` and `k = 2n (mod E)`.

The needed gcd estimate is valid, without a coprimality assumption:

```
H = 4Y(X+1)+3,
gcd(Y,H) = gcd(Y,3) <= 3,
gcd(XY,H) | X*gcd(Y,H),
E/gcd(E,H) >= Y/3 > R.
```

For the divisibility in the third line, multiply a Bezout identity for
`gcd(Y,H)` by `X`; every common divisor of `XY` and `H` divides its
right-hand side. Thus the weaker carrier congruence implies
`2n = R+1` modulo a modulus greater than `R`. The strict bound
`abs(2n-R-1) < R` turns this into equality. Only then does the recurrence
restore the full divisibility `E | k-R-1` and a positive quotient `h`.
The proof does not assume `h` while reconstructing the main rank.

The dependencies that still need formalization are substantial: signed
odd-index reduction, rational Pell saturation, and the calibrated native
compiler. In particular, a proof accepting only positive auxiliary `T`
cannot be substituted for the signed-quotient interface used after radical
recovery. Package 52 makes that last dependency explicit by mapping to the
preserved ordinary signed theorem.

## Packages 49 and 52: separation before recovering h

[Package 49](con-zfc-diophantine-forms/49-support-pell/sections/eleven.tex)
correctly identifies the incompatibility in simply combining packages 38
and 44: package 44's displayed estimate used `k>E`, which is unavailable
after deleting `h`. The repaired estimate needs only the authentic weak
outer bounds and `I=i*c^2`:

```
(I*g)^2-(c*f)^2 = I^2-c^2,
I*g-c*f > i*c/(8E),
(b+c*f)/d < 12/E < i*c/(8E).
```

Here the real roots satisfy `g<2Ec`, `f<2EI`, while `I>=c^2` and
`c>2Y>96`. This compares the actual auxiliary-root error with the coupled
root gap. It does not require the false intermediate assumption `k>E` or
the unnecessarily stronger inequality `I*g-c*f>1`.

[Package 52](con-zfc-diophantine-forms/52-sparse-pell/positive/Y_ABSORPTION_PROOF.md)
uses the same relative-error repair with the leaner carrier `K=IT` and
correction `ell`. Negative main-root exclusion remains valid because
`t+(k-R-1)/Y>0` and `(b0+g)/H>c/3>k`, whereas `tau<ell+k`.
Its inner rational recovery also checks the exceptional denominators:
`C(x)=0` would imply `Q | A(A-1)`, and `x=0` would imply
`Q | (A-1)^2`; both contradict `1<A<sqrt(Q)`.

The smaller absorption modulus is especially attractive for formalization.
The carrier now gives `Y | H(k-R-1)`, and the exact identity
`gcd(Y,H)=gcd(Y,3)` directly supplies `Y/gcd(Y,H)>R`.
After the same rank argument gives `2n=R+1`, the recurrence modulo `E`
restores `h`. There is no need to prove a stronger cancellation theorem.

Positive completeness of the lean carrier was also checked: its proposed
new coordinate satisfies

```
t >= gamma + T*(I*g-c*f) + (tau-ell) - h*X > 0,
tau-ell > k/3,       h*X < k/Y < k/3.
```

These are bounds for canonical witnesses, rather than an asserted
bijection on every positive assignment. The degree computation resolves
the leading cancellations before counting: the unabsorbed norm has degrees
`119,119,119,119,107,107,101,97`, summing to 888. Absorption contributes
`deg(Y^16)=64`, and the transport factor contributes 2, giving 954.
The unabsorbed twelve-positive product adds index and transport degrees
7 and 2, giving 897. The independent leading-form replay matches these
values and the displayed nonzero leading coefficient.

## Package 50: sound midpoint mechanism, dominated cost

[The midpoint proof](con-zfc-diophantine-forms/50-midpoint11/eleven/PROOF.md)
uses `U=4q^4` and a cleared carrier involving `ell+k/2`. It does not assume
that `k` is even prematurely: the first integral Pell norm proves evenness
before the half-integral correction is used. Its gcd bound is also sound.
The odd integer `H` is coprime to every prime divisor of `q` other than 3;
if 3 divides `q`, then `H=3 (mod 27)`. Therefore
`gcd(U,H)` is either 1 or 3, and `U/gcd(U,H)>R`.

This gives a different working quotient-absorption mechanism, but package
52 attains the same degree 954 with two fewer operations and a simpler
gcd step. There is no reason to choose 50 as the primary eleven-variable
formalization target when 52 is available.

## Package 53: the relaxed strong norm needs its own rank theorem

[The short proof](con-zfc-diophantine-forms/53-selective-quad/short/PROOF.md)
uses `(i*c^2)^2 = Delta*(f^2-1)`, in place of the normalized strong Pell
equation. Dividing an arbitrary supplied `i` by `Delta` is unjustified.
The manuscript correctly avoids doing so and proves a weaker rank theorem:

```
f = chi_A(m),   p | m,   c | m,
i*c^2 = Delta*psi_A(m).
```

The conclusion is not `c^2 | psi_A(m)`. The proof's key gcd step checks:
writing `psi_F(e*p)=S0*c` and `L=(F^2-1)*S0` gives

```
gcd(c^2,L*psi_F(e*p)) = gcd(c^2,Delta*c)
                        = c*gcd(c,Delta).
```

Since `c^2 | L*psi_F(t)`, this divides `L*psi_F(gcd(t,e*p))`.
The supplied large-ordinate bound `c>A*Delta^2` rules out a proper gcd
index by Pell doubling. After `p|m`, the recurrence congruence
`gcd(c,Delta)=gcd(p,Delta)` supplies the missing `c|m`.
The large-ordinate bound is established before either undetermined unit
sign is fixed, using `p>n>=24`; it is not a conclusion borrowed from
native decoding.

The deleted auxiliary quotient restoration also has the right order.
The rank theorem first supplies `c^2 | f^2-1` and `f>2c`; those facts make
the proof-only quantities
`o=cT-Rf` and `j=Tf-R*(f^2-1)/c-1` integral. Auxiliary Pell growth excludes
negative `V`, while `V=+/-1` contradicts `V=-c (mod f)`. Thus these
restored quotients are positive. Using the normalized formula for `j`
with the new multiplier would be a mistake; the text explicitly forbids it.

The ordinary rank argument and the inherited fixed-minus parity theorem
therefore remain the main new Lean obligations for P72/P74. A formal
same-coordinate theorem for normalized P75 cannot discharge them. The
manuscript's alternative canonical witness replacement is legitimate only
after rank and parity recovery; it is an existence equivalence, not an
identity on all supplied assignments. The resulting degree-80/72 point is
credible, but does not beat P67 on operation count or the degree-44 family
on degree.

## Replayed evidence and recommendation

All checks were run in extracted temporary archives, leaving imported
reports unchanged. The checks are evidence about literal coefficients,
circuits, and degree certificates; they do not decide consistency.

* Package 49: `eleven/verify_eleven.py` passed for the 990/117 and 994/115
  circuits, including full univariate degrees and analytic leading forms;
  `short/audit_offset44.py` passed for all 76 live gates, exact degree 44,
  three polynomial identities, and the coherent coefficient tuple.
* Package 50: `review/audit_midpoint_independent.py` passed all 72
  formal-radical products over three primes.
* Package 52: `positive/check_absorbed.py` passed 240 formal-radical
  products, 240 mod-4 guards, 120 positive-shift identities, 432 no-h
  bound cases, and all full univariate degree checks (954 and 897).
  The full sealed release runner passed on Python 3.12.13: 330 file hashes,
  132 source-blob checks, and all eleven isolated authored checks, including
  native coefficient checks, packing, shared-source symbolic checks,
  materialization, both nine-variable verifiers, the ten-integer verifier,
  and the remaining positive/leading-form/variant audits. Its three positive
  nine-variable points are degree 15,502,748
  in 548 operations; degree 10,486,092 in 603 operations; and degree
  10,127,484 in 655 operations. Natural-domain translations cost three more
  operations each.
* Package 53: `short/audit_relaxed.py` passed the literal 72/74/61-gate
  matrices, exact leading forms, all four coefficient payloads, nine
  inherited source blobs, historical Q56 comparison, and 32 unit-sign
  assignments.

The sealed package-52 runner has a Python-version portability issue. On
Python 3.13, the native coefficient regenerator changes gzip header byte 9
from `03` to `ff`, even with `mtime=0`. The raw integers and compressed
data after the header are identical, but the separate positive binding
retains the delivered gzip hashes. Consequently a full run reaches the
positive checker and fails its gzip hash check, even though that checker
passes on the untouched archive. This is a replay issue rather than an
algebraic counterexample; use the Python 3.12 environment for the sealed
replay, or preserve delivered compressed bytes when raw coefficients agree.

For eleven or twelve positive variables, formalize package 52's lean
carrier and Y-absorption. Start with its root/separation and gcd lemmas,
then supply the explicitly signed Pell/compiler interface. For a small
fifteen-variable evaluator, retain the independent degree/cost tradeoffs
and prefer the degree-44 family to local degree-64 P76 at comparable cost.
The lowest-operation route, now package 51's 66-operation equation, remains
a different objective. For the
already checked closed nine-variable construction, continue the independent
explicit compiler path and import sparse quadratic packing separately;
none of the local positive-family algebra supplies the separate theorem
connecting the reports' native compiler to ZFC refutations.
