# Independent review of the 86-record positive-gap candidate

This review concerns the frozen layout with 31 positive source variables,
22 quadratic residuals, 86 weighted records, maximum input exponent 100,
kernel degrees `(1545, 1920, 1847)`, convolution height 2047, and maximum
target exponent 2016. It applies to both the complete original31 coefficient
tuple and the complete native44 coefficient tuple, with their respective
base and threshold constants. It does not authorize mixing coefficient
ports between these instances.

## 1. What was checked independently

`check_positive_gap.py` uses the Python standard library and imports no
project code. It reconstructs all 22 residuals from the supplied original
60-gate circuit, treating the four coefficient ports as independent symbols.
It then applies the explicit substitutions and row operations below,
reconstructs all 86 weighted records, and checks every target extraction
against the complete constant, linear, and quadratic monomial bases.

The check covers all 22,451 degree-matched interactions. There are no
unintended target interactions. It independently recovers the stated kernel
degrees and height, verifies that the leading coefficient of the quadratic
kernel is exactly `+1`, and verifies that residual 5 takes the value 1 on
the all-one source tuple. The latter implies that every common source zero
has at least one coordinate greater than one.

It also independently computes the coefficient majorants from all merged
kernel coefficients. The report is `positive_gap_independent_check.json`.
The authenticated source, record, and layout hashes are recorded there.
These are finite algebra and finite combinatorial checks, not a verification
of an unbounded consistency theorem.

## 2. Positive source-coordinate changes

Write `k=eta+zeta` and `Y=a-E`. The old rows imply

    Y=sN>0,       c-eta=kY>0,       P-k=E(c-eta)>0.

Define the new positive coordinate `p=P-k`. The old first norm is

    tau^2=P(P-k)+1=p^2+kp+1>p^2.

Since the supplied `tau` is positive, `t=tau-p` is positive. Conversely,
the substitutions `P=p+k` and `tau=p+t` send the new rows

    p-E(c-eta)=0,
    t^2+2pt-kp-1=0

exactly to the old rows. No other row contains `P` or `tau`; the independent
symbolic check verifies this fact directly from the original circuit.
This is a bijection of positive zero sets, not only a formal substitution.

The new square register is `L_new=L_old+1=q^2`. Since the authentic ports
have `beta>0` and `J>0`, `q=beta J+1>1`, so the inverse register
`L_old=L_new-1=q^2-1` is positive on every new zero. Substitution proves
the other rows exactly. Finally replacing rows 14 and 15 by their sums
with rows 2 and 3 respectively is invertible on common zero sets.

### The transport variable must be stated explicitly

The historical source60 circuit uses the shifted coordinate `z_s`, whereas
the 86-record source uses `z_o=z_s+1`. Its exact transport relation is

    (K0+w)C+(q-F)-z_o(q-1)=1,

equivalently

    (K0+w)C-F=(z_o-1)(q-1).

Substituting `z_s=z_o-1` in the original source60 residual adds `+beta J`
to that residual. The independent reconstruction explicitly includes this
term. Omitting it would describe a different polynomial.

The inverse shift is positive by the inherited old-source Pell argument,
not merely by the displayed polynomial identity. That argument first
establishes `C>0`, `q>1`, `F<q`, `X=wq=2^R`, and `R>3q` on old source
zeros. In particular `2^R>q^2`, hence `w>q>F`. Therefore
`(K0+w)C-F>0`, and the transport identity forces `z_o>=2`. Thus
`z_s=z_o-1>0`. This uses established source soundness consequences in the
same order as `QUARTIC60_PROOF.md` and the retained59 proof; it does not
derive `C>0` by assuming a decoded word in advance.

## 3. Coherent native44 substitution

Section 7 of `upstream44/native/PROOF.md` supplies the same 16-variable
retained Pell system as the ancestor of source31, including its shifted
transport equation `(K0+w)C=F+z_s(q-1)`. Its native-interface theorem is
proved for the entire compact tuple. All four ports must therefore be
rebound together, with `MF` equal to the shifted source mask.

The projection from a positive source31 zero to this 16-variable system
follows from its defining quadratic register equations. Conversely,
completeness may use the canonical native/Pell witnesses supplied by the
inherited construction. All added source31 registers are positive on those
witnesses. The only extra positivity that is not immediate from a product
or square is the register `g_aux=y^2-V^2`. The canonical auxiliary data
have `I>1`, `R>=3`, `V=chi_I(R)/I>1`, and

    I^2 V^2-(I^2-1)y^2=1.

Consequently `(I^2-1)g_aux=V^2-1>0`, so `g_aux>0`. The canonical lift,
projection, transport shift, and positive gaps give existence equivalence
for the entire native44 tuple. This is not a claim that packed witnesses
for the old and compact tuples are identical.

## 4. Coefficient constants and unconditional positivity

Let `mu` be a bound strictly greater than the absolute value of every
coefficient of every merged kernel. The independently recomputed choices
are as follows.

| Whole tuple | Port bit lengths | `mu` | `kappa` |
|---|---|---|---|
| original31 | 1064921, 1070004, 1064921, 1064922 | `2^2134927` | 2134939 |
| native44 | 590069, 592884, 590069, 590070 | `2^1182955` | 1182967 |

In both cases set

    B=2^kappa b^2=4096 mu b^2,
    ell=sum_i B^w_i,           U=ell+g,
    G=D2(B)U^2+D1(B)U+D0(B),
    Targets=sum_j B^t_j,
    N0=B^101,                 Z=B^2048,
    Mask=N0-1-(b-1)ell,
    Jcode=2G+Targets,
    S=g+N0 Jcode,
    T=Mask+N0(B-2)Targets.

The outer inputs `b,g` are positive. Since `ell>=B^100`, one has
`U>=B^100`. The head of `D2` is exactly `B^1847`, so

    D2(B)>B^1847/2,
    |D1(B)|<2 mu B^1920,
    |D0(B)|<2 mu B^1545.

Relative to `B^1847 U^2`, the two possible negative contributions are
bounded by `2mu/B^27` and `2mu/B^502`, respectively. Each is less than
`1/8`, giving `G>0` for every positive outer assignment, before any bound
on `g` or power-of-two conclusion. The mask has base-`B` digits `B-b` at
the 31 input positions and `B-1` elsewhere, so `0<=Mask<N0`. Therefore
`S>0` and `T>=0` unconditionally.

Put `L=b B^2149` and `R=L(S+T+1)-S-1`. Then

    R=(L-1)S+LT+L-1>=L-1>=8.

Both `b<=R` and `b<=N`, together with `N>=8`, hold for either threshold
constant below. Thus the unchanged ratio theorem's unconditional size
hypotheses are available without assuming binary decoding.

## 5. Bounded words, sparse borrows, and completeness

On the ratio-soundness branch, `8g<Gcap=32bB^100`, so
`g<4bB^100<N0`. Also `ell<2B^100` and `U<6bB^100`. The geometric
coefficient bounds and convolution height 2047 give

    |G|/Z < 43 mu b^2/(B-1),
    2G < Z/32.

Indeed `B-1>2752mu b^2`, and the three terms contribute bounds with
numerators `36`, `6`, and `1`. Since every target is at most 2016,
`Targets<Z/64` and `(B-2)Targets<Z/64`. Along with `g,Mask<N0`, these
give, with ample strict slack,

    S+T<N0 Z=B^2149<=L.

For binary `b=2^k`, the low-mask test decodes exactly a word
`g=sum_i z_i B^w_i` with `0<=z_i<b`, and the source coordinates are
`y_i=z_i+1`. Every coefficient `h_t` of the convolution at these source
coordinates satisfies

    |h_t| < mu*((sum_i y_i)^2+sum_i y_i+1)
          <=993 mu b^2 < B/4.

This bound includes all unmarked coefficient collisions. At each target
the finite isolation proof gives `h_t=2rho_j(y)` exactly.

The high word has signed digits `2h_t+delta_t`, where `delta_t=1` at
targets and zero elsewhere. The above bounds imply that incoming borrows
are only 0 or -1. At a target, `h_t=0` produces normalized digit 0 or 1;
every nonzero `h_t` produces a digit with some bit in common with `B-2`.
The high mask therefore tests precisely the simultaneous source equations.
The positive and bounded words ensure that this is finite nonnegative
binary arithmetic, with no bitwise convention for negative integers.

Conversely, given any positive source zero, choose an arbitrarily large
power of two `b` exceeding all its coordinates and set
`g=sum_i(y_i-1)B^w_i`. The all-one check gives `g>0`; also
`g<bB^100`, hence the stronger completeness condition `32g<Gcap`.
The low and high masks are disjoint from the encoded word. Thus the source
equivalence is preserved with the exact strict ratio bounds required.

## 6. Population threshold, including b=1

For `b=2^k` write `B=2^v`, where `v=kappa+2k`, and `L=2^u`, where
`u=k+2149v`. The two nonoverlapping blocks of `T` have populations

    pc(T)=101v-31k+22(v-1)=123v-31k-22.

The bounded-word identity

    R=(S+T)L+(L-1-S)

therefore yields

    pc(R)=u+pc(T)-tau,
    tau=pc(S)+pc(T)-pc(S+T)>=0.

Set

    N=2^c b B^1128,          c=8kappa-11.

Thus `c=17079501` for original31 and `c=9463725` for native44. Directly,

    u+pc(T)=2272v-30k-22=2(c+k+1128v)=2log_2(N).

Legendre's identity `v2(binomial(2R,R))=pc(R)` gives
`N^2 | binomial(2R,R)` precisely when `tau=0`, equivalently when `S` and
`T` are bitwise disjoint. This calibration is an identity for every integer
`k>=0`. In particular no excluded `b=1` case is hidden in the proof.
That case cannot be a final solution: its low mask is `N0-1`, while the
ratio bound gives `0<g<N0`, hence a nonzero masked low bit.

## 7. The inherited positivity-first finalizer

The finalizer itself is the same as the package59 free-carrier adjunct.
The preceding sections reestablish all source-dependent premises after
the changed source and exponents. Its two numerical Jones interfaces are
still inherited theorems: soundness uses `8g<Gcap`, and completeness uses
`32g<Gcap`. They are not proved by enumerating finite examples here.

The free-carrier and radical arguments were checked at the level of the
displayed identities. In the inherited notation, for all positive outer
inputs one has `E0=J(n+W1^2)+Q>0`, `V0^2>a0`, and `V1^2>64a1`.
Consequently a final zero first forces the normalized margin `m>0`.
Only then is the old carrier range recovered; it gives `a1>a0` and
excludes a zero sum of signed radicals. A rational nonzero sum of the two
square roots makes each root rational, hence integral. This supplies the
square and divisibility conditions required by Jones soundness. The exact
CRT coordinate uses `j0=j-1>=0`, as in the inherited proof.

Completeness chooses the signed-root factor with positive roots and uses
`W1^2+Q/J<2D<V1` to make
`n=m(V0+V1+r0+r1)-W1^2-Q/J` strictly positive. The quotient shift
therefore preserves the stated strictly positive domain. None of these
arguments changes when the new `R,N,Gcap` satisfy the premises just proved.

## 8. Exact degree

Let `a=2^kappa` and `cstar=2^c` denote positive fixed constants. On the
diagonal where all nine outer inputs are the same indeterminate, the new
source data give

    deg(S)=4296, head(S)=2a^2148,
    deg(L)=4299, head(L)=a^2149,
    r=deg(R)=8595, head(R)=2a^4297,
    q=deg(N)=2257, head(N)=cstar*a^1128.

The source of the final leading cancellation is removed by the exact
identity in the inherited certificate form. Its dominant inner term is
`Omega^2 Delta1`, of degree 898898. The competing final subtraction has
degree 1304252, below twice this value. Equivalently the total degree is

    104r+400q+8W+316=1,797,796.

For an independent leading-coefficient calculation, write
`r0=2a^4297` and `n0=cstar*a^1128`. The finalizer's dominant diagonal
coefficient is

    2^82 a^(4W) r0^104 n0^400
       =2^186 a^898488 cstar^400>0.

The diagonal therefore attains the multivariate upper bound on either
complete coefficient slice. Positivity of the fixed constants makes this
degree assertion independent of accidental lower coefficient cancellations.
The 465-operation count belongs to the emitted live binary circuit; its
full circuit replay and liveness audit are separate deliverable checks.

## 9. Semantic and formal trust boundaries

Three different conclusions must not be conflated.

1. The local coordinate transformations, finite isolation certificate,
   coefficient bounds, population calibration, and finalizer composition
   prove the new instance equivalent in solvability to its specified
   inherited arithmetic source, using the explicitly identified numerical
   Jones/Pell interfaces. These ordinary arithmetic arguments are suitable
   for internalization; no consistency assumption is used in them.
2. The historical native/compiler and K215 calibration documents claim an
   ordinary semantic bridge between that source and a finite refutation.
   The present audit retains those dependencies. It does not reprove the
   whole machine/tableau/compiler development from its literal transitions.
3. The repository's current `OBJECT_ZFC.md` explicitly distinguishes its
   external Lean equivalence from an object-language ZFC proof and states
   that the internal iff remains open. Its `KEndpoint`/constructible-choice
   bridge is external, and numeral agreement does not cover nonstandard
   internal natural witnesses. A new `BProv` endpoint is not supplied here.

Absence of a proof-assistant certificate alone would not invalidate a
complete ordinary mathematical proof that ZFC derives an equivalence.
However, an external standard-natural equivalence alone does not imply
that derivability statement. The accurate unconditional output of this
local audit is the arithmetic delta theorem. A corollary asserting the
requested internal ZFC iff must explicitly assume, or separately establish,
the inherited proof-code calibration and arithmetic/compiler correctness
for every model's internal naturals. This review neither declares those
open obligations solved nor claims that they cannot be solved.

The delivered equation is an improvement of the inherited explicit
construction. It is not a proof of consistency, a global minimality
result, or a new construction independent of K215 and Jones.
