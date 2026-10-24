# Peer review: batched direct certificates

Status: **PASS for the ordinary direct/common-frame and integer arguments,
literal equations, and finite replays.** No new mathematical gap was found.
This review covers the direct and integer components of
`con_zfc_batched_certificates_2026-10-23.zip`; the separate thirteen-integer
supplement is being reviewed independently and is outside this note.
Lean formalization remains paused.

The archive SHA256 is
`ff0d3f638d91a905f676f6fe3e40e134979a14880ed34cadf0741604386e8e55`.
All 233 files, totaling 12,213,562 uncompressed bytes, were safely extracted
to scratch and authenticated against the original ZIP. The complete
232-entry delivered manifest passes normally and with optimized Python.

| Literal equation | Domain | Variables | Rows | Degree | Quartic monomials | Height |
|---|---|---:|---:|---:|---:|---:|
| Common radix | Naturals | 2,108 | 1,745 | 4 | 10,629 | 127,777,275 |
| Common radix plus offset | Naturals | 1,968 | 1,717 | 4 | 10,545 | 127,777,275 |
| Shared frame | Naturals | **1,153** | 1,021 | 4 | **9,234** | **127,778,299** |
| Compact default | Naturals | **667** | 535 | 4 | 23,747 | 2,649,643,818,040 |
| Compact support alternative | Naturals | **680** | 548 | 4 | 18,302 | 690,871,812,080 |
| Signed companion | Integers | **1,690** | 842 | 4 | 21,381 | 2,649,643,805,758 |

The 667-variable point trades larger coefficients/support for fewer
variables. The 680- and 1,153-variable points remain useful alternatives.
The 1,690-integer endpoint reduces variables substantially relative to our
6,604-integer row-guard checkpoint while raising coefficient height from
127,299,660 to 2,649,643,805,758. These are multiple cost measures; no
global simplicity or minimum-variable claim follows.

## Common radix and signed quotient offset

For assigned natural upper arguments `n_l`, set `S=sum n_l` and
`Q=2^S+1`. Every coefficient in `(Q+1)^n_l` is at most `2^n_l<Q`,
so the expansion is a genuine carry-free base-`Q` expansion. The three
natural equations

```
P=D(Qh+c)+r,  D=r+u+1,  Q=c+v+1,
P=(Q+1)^n,    D=Q^k
```

identify `r` as the remainder modulo `D` and `c` as the next base digit.
They recover `c=binom(n,k)`, including zero when `k>n`. Nonnegative
`h,r,u,v` give all Euclidean bounds; no unstated integrality or digit
condition is used. The sixteen actual lower arguments have only four
literal values, giving 21 binomial-related power calls rather than 48,
and 28 power calls overall rather than 55.

For finitely many congruences `L_i+M_i q_i^+=R_i+M_i q_i^-`, choose
one natural `O>=max q_i^-` and replace their quotients by
`q_i=q_i^++O-q_i^-`. This gives
`L_i+M_i q_i=R_i+M_i O` simultaneously; the converse chooses
`q_i^+=q_i,q_i^-=O`. The argument works even with zero or negative
moduli. In this natural compiler the later moduli have their usual
positive interpretation, but the offset lemma does not assume it.
The exact request-dependency audit also confirms that this offset enters
no semantic power base, exponent, or proposed output, so it can be chosen
after the shared number-theoretic frame.

## Shared Pell-frame soundness

For the 28 assigned requests `(n_i,k_i,m_i)`, the literal global bound is

```
W=1+sum_i(n_i+k_i+m_i).
```

It includes every proposed output, independently of whether that output
is correct. The finite ledger has 23 groups of identical exponent atoms;
every request points to the exact matching group. No equality is inferred
from numerical sampling. The independent peer checker reconstructs the
actual `W` gate as the complete sum of all 84 input/exponent/output
ports, with multiplicities, and verifies that no Pell-frame coordinate
enters the requests.

The actual builder retains `A=a0+2`, hence `A>=2`. Its last norm is

```
A^2=1+W^3(W+2)Z^2.
```

Since `W>=1`, `Z=0` would give `A=1`. Thus `Z>=1` and `A>W`.
All proposed outputs satisfy `m_i<W<A` before any individual power
representation is interpreted.

Every group has `Y_j>=e_j>0`. Let `P=product_j Y_j`. The pooled auxiliary
coordinate is `V=P^2(d+1)`, so for every group it is positive, divisible
by `Y_j^2`, and at least `Y_j`. The literal builder uses
`B=1+4P(b+1)`, stronger than the paper's displayed `B=1+4Pq` with
`q>=0`. It therefore already forces `B>1` and supplies the required
congruence modulo every `4Y_j`. There is no mismatch in completeness:
its CRT solution has `B>1`, so its quotient `(B-1)/(4P)` is at least
one and has exactly the literal `b+1` form.

The paper's more general recovery of `B>1` is also sound: if `B=1`,
the group norm gives `S_j=1`. The two `A`-norms and `V>=Y_j` imply
`U>=X_j>=A>=2`; then `U|(X_j-1)` contradicts `0<X_j-1<U`.
All hypotheses of the established indexed-Pell criterion hold group by
group before any power base is interpreted.

For a positive base `n_i`, the assigned local modulus satisfies
`T_i=2An_i-n_i^2-1`. Since `A>=n_i+1`,

```
T_i-A >= (n_i+2)(n_i-1) >= 0.
```

Thus `m_i<W<A<=T_i`, recovering the omitted strict output bound.
The bound also restores both input inequalities `n_i,k_i<=W` and
ordinary subtraction `A-n_i`. The established positive-power criterion
then gives `m_i=n_i^k_i`. The inspected primary implementation is
Mathlib's local `NumberTheory/PellMatiyasevic.lean`, theorems
`matiyasevic`, `eq_pow_of_pell_lem`, and `eq_pow_of_pell`; it was read
inertly and no Lean command was run.

## Simultaneous completeness and the pooled period

First choose the true semantic outputs of the finite original arithmetic
certificate. They determine the sixteen binomial upper arguments and
then the common radix. All requested power inputs and correct outputs
are now fixed, before selecting a Pell frame or congruence offset.

Form `W` from these values and choose
`A=chi_(W+1)(W)`, `WZ=psi_(W+1)(W)`. The standard congruence
`psi_a(s)=s mod(a-1)` supplies the integer `Z`, and
`n_i^k_i<=n_i^W<(W+1)^W<=A`. This is the usual cofinal power
construction with a common bound instead of `max(n_i,k_i)`.
It gives every required local modulus and power congruence at once.

Set `X_j=chi_A(e_j)`, `Y_j=psi_A(e_j)` and form their product `P`.
The matrix

```
M=[[A,A^2-1],[1,A]]
```

has determinant one modulo `4P^2`, so it belongs to a finite group of
invertible matrices. A positive period exists. Choose a multiple `L`
larger than every `e_j` and larger than one. Its Pell coordinates give
`U=1 mod 4P^2` and `V=0 mod 4P^2`, with `V>0` and `U>A`.
In particular `P^2|V` and `gcd(U,4P)=1`. This proves the actual pooled
divisibility; separate statements `Y_j^2|V` would not suffice because
the ordinates can share primes.

Finite CRT now gives `B=A mod U` and `B=1 mod 4P`. Its least
nonnegative solution is at least `A`, because `A<U`; hence `B>1`.
Choose the nonnegative `d=V/P^2-1` and `b=(B-1)/(4P)-1` used by
the literal implementation. Pell recurrences give
`chi_B(e_j)=chi_A(e_j) mod U` and
`psi_B(e_j)=e_j mod 4Y_j`. All frame conditions are satisfied
simultaneously. Finally choose the shared quotient offset large enough
for all resulting congruences. None of these existential choices changes
the previously chosen semantic outputs.

## Positivity before deferred arithmetic interpretation

All exponents are positive from the actual natural gate graph before
any power theorem is applied. Hence group-index recovery and pooled
positivity come first. Twenty-seven power bases are also structurally
positive. The only exception is the proposed factorial output `T` used
as a later power base.

Apply the local power argument to those 27 bases. This makes the
factorial numerator `Pnum=(radius+1)^H` positive. The exact ceiling rows

```
Pnum+c=c*T+r+1,  c=r+s+1
```

would imply `Pnum=-s<=0` if `T=0`. Thus `T>=1`, and the remaining
power call is licensed. Both factorial numerators and all 28 powers
are therefore interpreted before the common-radix digit theorem is
used to recover all binomial values. The digit bound uses the assigned
natural upper arguments; it does not presuppose their later factorial
meaning. This resolves the deferred graph cycle.

The provided builder-free audit verifies this order on the actual call
sites: the first round proves `pow0,...,pow3,pow5,...,pow27` and
factorial positivity by the ceiling equations; the second proves only
`pow4`. The independent mathematical argument above is unbounded; the
small frame fixtures are not substitutes for it.

## Natural and signed monic projections

The 667- and 680-variable natural endpoints delete only coordinates with
exact defining rows `v-f=0` or its negative and nonnegative-coefficient
restoration `f`. Every deleted value is therefore a natural number for
every natural target assignment. Full substitution checks keep every row
quadratic. Reverse chronological restoration gives the inverse map.
The default endpoint has 486 checked steps, 156 affine and 330 quadratic;
the support alternative has its separate complete certificate.

For integers, the construction correctly starts from the full
1,153-coordinate shared frame. It appends three-square guards to all
358 original nongates. The actual 795 gate definitions are monic,
nonnegative, and triangular, forcing all original coordinates natural
at arbitrary integer zeros. Legendre's theorem supplies every guard
in the other direction, including zero.

Only then are 537 signed monic substitutions performed, 308 affine and
229 quadratic. Negative restoration coefficients are allowed over the
integers. They are substituted into every affected residual, including
sign guards. Reverse restoration recovers the complete guarded parent
before its nonnegativity proof is applied. All final residuals remain
quadratic; the full collected polynomial has exact degree four. No
unconstrained coordinate is silently dropped in the delivered schedules.

## Replays and provenance

All four complete component runs pass: direct normal/optimized with
`--rebuild` compare sixteen primary files, and integer normal/optimized
with `--rebuild` compare six. The integer wrapper launches its rebuild
child without forwarding `-O`; I additionally rebuilt its builder and
optimizer explicitly with `-O` and obtained the same six files. Thus
the optimized rebuild claim is not inferred from the wrapper alone.

All 45 retained upstream `direct/` and `report/` members match the
authenticated original shared-certificates ZIP, SHA256
`61582dab90e880049e61ff1a5c49386747cd063de15e18411a20f327b9559ba1`.
The integer component's frozen natural parent matches the delivered
shared-frame equation byte for byte. It uses the same C222 source,
free truth code zero, and contradiction code one; no machine coefficient
tuple is mixed into the direct construction.

The separate `batched-direct-peer.py` imports no delivered module. It
authenticates all 233 original members, independently expands all six
ordinary quartics, checks their domains and complete coordinate lists,
and reconstructs the shared-frame exponent/group and bound ledger.
Normal and optimized receipts agree apart from the mode field.
The supplied independent projection checkers also reject corrupt
restorations and a missing input guard; the literal fixture rejects a
changed power output. No archive or delivered file was modified.

The mathematical dependencies remain the named C222-to-ZF calibration,
constructible-choice refutation bridge, and classical Pell results.
This ordinary review supports adopting the batched arithmetic architecture
as a concrete smaller direct route. It does not provide the outstanding
fully checked internal object-ZFC derivation or prove Con(ZFC), and it
does not claim global variable or coefficient optimality.

As a separate improvement lead, a read-only elementary row-closure probe
on the 1,153-coordinate checkpoint reduces its 358 guards to 317, giving
2,104 coordinates before signed projection instead of 2,227. That probe
is not a materialized new endpoint and is not included in any table above.
