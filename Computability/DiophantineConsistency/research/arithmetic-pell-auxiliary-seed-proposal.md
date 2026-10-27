# Internal positive auxiliary witnesses from the squared Pell seed

Read-only proposal, 27 October 2026. No new Lean source, overlay, prerequisite
refresh or compiler has been created for this checkpoint. Proposed pair:
`ArithmeticPellAuxiliarySeed` and Checks, with exactly these imports:

```
DiophantineConsistency.ArithmeticPellSquaredSeed
DiophantineConsistency.ArithmeticPellHalfIndex
```

The target is the displayed fourteen-variable carrier's positive auxiliary
witnesses. The signed thirteen-variable carrier and its additional free-variable
positivity constraints are outside this pair. Outer simultaneous Pell witnesses,
internal native encoding and final PA/HA assembly remain separate.

## Public endpoint

All values below belong to the same arbitrary-universe IΣ1 arithmetic model.
For arbitrary `a R : V` with only `R % 4 = 3`, put `c := ycoord R a`.
The proposed `auxiliary_seed` returns `f i T u y : V` with:

```
0 < f, 0 < i, 0 < T, 0 < u, 0 < y,
f = xcoord (R*c) a,
ycoord (R*c) a = i*c*c,
f*f = 1 + delta a*(i*c*c)*(i*c*c),
I := delta a*i*c*c,
y = ycoord R (I-2),
xcoord R (I-2) = I*u,
u = oddQuotient ((R-1)/2) (I-2),
f*f*c*T = u+c+f*f*R,
u = absdiff (f*f*c*T) (f*f*R+c),
I*I*u*u + y*y = 1 + I*I*y*y.
```

The displayed lets abbreviate values, not extra hypotheses. In particular,
there is no supplied strong norm, desired divisibility/residue, coprimality,
auxiliary norm, generic finite-pigeonhole claim, or desired quotient identity.
The accepted SquaredSeed constructs the actual `f,i`; it is not just used as
an existence oracle with an unproved premise. Rank positivity and `R>=3` follow
from the phase. `a=0` is legal, so the construction also covers offset base two.
No evenness of `a+2`, oddness of `c` or `i`, or large-ordinate bound is needed
for these fourteen-variable witnesses.

The additive literal identity is the primary interface. Its positive `u`
shows which order holds in the natural absolute difference, avoiding an
unjustified subtraction or silent conversion from signed integers. If useful
and short, the same identity can additionally derive `R<c*T` and the literal
truncated expression `u=f*f*(c*T-R)-c`; this follows only after proving the
requisite order and is not needed to supply the maintained absdiff factor.

## Exact missing residue interface

HalfIndex already exports the represented `oddQuotient`, its exact product,
base cases `odd_zero`/`odd_one`, and `odd_rec`. It exports `odd_y_rec` and
`y_three` for the original ordinate. However, `quotient_mod_norm` returns only
`SignMod f`, and both existing modular conclusions discard which sign occurs.
They cannot be substituted for the needed result modulo `f*f` with its negative
phase. The new proof must retain this information explicitly.

Write `Q(h)=oddQuotient h (I-2)` and `Y(h)=ycoord (2*h+1) a`.
For `I>=2`, `f>0` and the derived identity

```
I*I + delta a = delta a*f*f,
```

prove a genuine Sigma1 induction on the internal variable `t` for the pair

```
Q(2*t) % (f*f) = Y(2*t) % (f*f),
(Q(2*t+1) + Y(2*t+1)) % (f*f) = 0.
```

The exact coefficient equation is

```
4*I*I + 4*(a+2)*(a+2) = 4 + (f*f)*(4*delta a).
```

It works modulo `f*f` directly; no square-root cancellation occurs. The initial
negative pair uses `Q(1)+ycoord 3 a=(f*f)*(4*delta a)`. The positive pair at
zero is `Q(0)=ycoord 1 a=1`. Two successive uses of the additive recurrences
carry one equal-residue pair and one opposite-residue pair to the next even
and odd quotient indices. The existing `transport_equal` and
`transport_opposite` in HalfIndex are private. This new leaf will prove the
small finite modular-cancellation step locally, using the public
`ArithmeticPellResidueClasses.mod_add_cancel` and actual add/multiply remainder
identities. It will not call private mangled names or edit the accepted module.
The helper concerns only finitely many arithmetic values and recurrence
equalities; it does not postulate a semantic sequence or unrestricted induction.

The same two-step induction with the comparison sequence `L(h)=2*h+1` gives

```
Q(2*t) % c = (4*t+1) % c,
(Q(2*t+1) + (4*t+3)) % c = 0,
```

under `c>0` and `c|I`. Its coefficient comparison uses `c|4*I*I`, its first
negative pair is `Q(1)+3=4*I*I`, and the linear sequence's additive recurrence
is a finite polynomial identity. These are positive-modulus congruences with
explicit orientation; neither a generic SignMod oracle nor an assumed phase
of an existential disjunction is used.

The two public oriented residue helpers may retain their explicit generic
norm/divisibility hypotheses. `auxiliary_seed` discharges every one from its
actual squared seed and `c=ycoord R a`. All induction predicates use only
represented Pell coordinates, natural division/remainder and fixed polynomial
operations with existential or conjunction closure. The induction is the
existing IΣ1 schema, not induction on arbitrary Lean predicates.

## Constructing all actual witnesses

1. `R%4=3` and `div_add_mod` give `R=4*(R/4)+3`, hence `R>0`. With
   `t=R/4`, set `h=2*t+1`. Elementary ordered subtraction and division give
   `R=2*h+1` and `h=(R-1)/2`.
2. Set `c=ycoord R a>0` and call `SquaredSeed.strong_seed R a`. Its explicit
   index is `R*c`. The returned norm and positive `i,c`, together with
   `delta a=(a+1)*(a+3)>=3`, give `I>=2` and
   `I*I+delta a=delta a*f*f`. Also `c|I` follows from the literal product.
3. Set `u=Q(h)` and `y=ycoord R (I-2)`. The exact odd product gives
   `xcoord R (I-2)=I*u`; positive x-coordinate and positive I give `u>0`.
   `R<=y` gives `y>0`. The residue pairs at `t` now give
   `(u+c)%(f*f)=0` and `(u+R)%c=0`.
4. Extract `o` from `u+c=(f*f)*o`. Since `u+c>0`, `o>0` follows. The strong
   norm gives the exact additive identity
   `f*f=1+c*(delta a*i*i*c*c*c)`. Writing the last coefficient as H,
   `u+c+R=(o+R)+c*(H*o)`. Since c divides `u+R`, it divides the left side,
   and removal of the divisible summand yields `c|(o+R)`. This is an exact
   elementary division argument; no CRT or supplied coprimality is needed.
5. Choose the actual quotient `T=(o+R)/c`. Then `c*T=o+R`, and positivity
   of its right side implies `T>0`. Multiplication by `f*f` gives exactly
   `f*f*c*T=u+c+f*f*R`, from which the stated absdiff binding follows.
6. The actual norm at base `I-2` and index R, with
   `delta(I-2)+1=I*I` and `xcoord R(I-2)=I*u`, gives the final additive
   auxiliary norm by semiring algebra. Every subtraction involving `I-2`
   was first justified by `I>=2`.

Likely size is approximately 300–420 main lines and 50–70 Checks, including
the local finite modular step. The public construction is one coherent leaf;
if this unexpectedly requires a new dependency or separate checkpoint, report
that exact change before a compiler invocation. Focused checks should bind the
full arbitrary-model endpoint, both oriented residues, rank phase three,
`a=0`, the actual strong-seed coordinates and positive T/absdiff orientation.
No large closed Pell numeral reduction is necessary.

## Exact accepted cache union

The read-only inventory is `arithmetic-pell-auxiliary-seed-cache-plan.json`, SHA
`59de0e399ed01693294f7c5d6363287c5268797619abc9a2f4b42b0f7ebc3e35`.
It authenticates 108 cached modules, 95 Foundation, 393 custom artifacts,
38 boundary primaries plus 76 companions, and all 507 first providers.
No new Foundation module or prerequisite refresh is proposed. All 99 overlapping
cached modules in the two parent inventories match source and every artifact.
All current headers and the reachable DAG were checked. The read-only audit
made 6,127 comparisons over 1,916 paths and created no overlay or compiler job.

Accepted HalfIndex provider:
`/tmp/arithmetic-pell-half-index-root-qso00172/lib`, source
`222bc3bd7e7fbb2c4924fee0b26c24f38e359475b956fd800116b1abe665871c`,
main object
`ba6797b357acfc6c59a0fceaccb58a8f0164bb7a51b25d2b2abdfcec626f6c79`.
Accepted SquaredSeed provider:
`/tmp/pell-squared-seed-controller-peer-n40xllwf/lib`, source
`c12b5f7c746ee1df1d111814b10db039049992f6b8d2cc3b8f8857cfd95510d8`,
main object
`76f5a3d2fe6f118be216894486ee08f4831e8e47aa17286202020e3e8d46c2d4`.
Both complete result packets, manifests, source snapshots, command/log records
and ROOT acceptance notes are pinned. I independently replayed SquaredSeed;
I did not author it or HalfIndex. This proposal is not an independent fresh
rebuild of their prerequisites or a proof of the proposed new theorem.

Before any authorized future compile, read the entire new pair and executed
driver, snapshot both inputs first, reauthenticate this exact source/provider
closure, and use only two fresh regular leaf outputs under Lean4.32
`-M6000 -j1 -DElab.async=false`, one thread and the 512MiB reserve.
Retain all failures and immutable input/log/command/object evidence. No current
Lean source, shared object, Git state or accepted receipt is edited by this plan.
