# Wave11 positive-endpoint review

This review covers the positive-integer endpoints in four newly arrived
packages, plus the twelve-variable section of the separate manuscript
`report.zip`. It does not review their unrestricted-integer or nine-variable
results. The immutable intake trees under
`/tmp/dioph-wave11-arrivals-9a33342a03` were read, then copied to separate
scratch directories before selected Python replays. No Lean work was run.

The new positive reductions have coherent ordinary mathematical proofs on
their stated strictly positive domains, relative to their explicitly
inherited compact44 native/compiler calibration. All eight delivered
positive circuit packets passed independent topology, liveness, whole-tuple
and actual-coefficient degree-specialization checks. Selected authored
audits passed normally and under `-O` in 26 stages. This is not a claim of
full multi-component release replay, end-to-end Lean verification, or an
encoded internal-ZFC derivation.

## Intake pins and verified endpoints

Archive SHA256 values, independently checked against the actual incoming
ZIP bytes, are:

| Archive | SHA256 |
|---|---|
| `ConZFC_Structural_Reductions_Round11_2026-10-24.zip` | `83bccd59ab691f7076a36c2b03cf84f05f8f7b2c04490ede94c389c29ec2034d` |
| `con-zfc-budget-and-centering-2026-10-23.zip` | `a23fb49828081f072375f00eeaa37e7d45f6d1bcfbb9ec0eb8850d124600e34b` |
| `con-zfc-centered-pell-norms.zip` | `6b176f4e5db4b8a4ec7a7357f3ab3f8356cc811ad7fe65b0ac748c1047812fcd` |
| `ZFC_Diophantine_Joint_Guards_2026-10-24.zip` | `291af5f4266ba5e0759273282ef4c6c5941f0bd2c3813e0481b721b08605b159` |
| `report.zip` | `4130601f3f13426318c4266a87e2d6ce9cf7205c711a9c226782e87744be2754` |

All numbers below use the supplied convention: each live binary addition,
subtraction or multiplication counts once, including squaring and scalar
products; fixed leaves and reuse are free.

| Proposal | Positive unknowns | Operations | Exact degree | Status |
|---|---:|---:|---:|---|
| Structural round11 `positive/p11_degree277.json` | 11 | 111 | 277 | Delivered literal; selected audits pass |
| Structural round11 `positive/p12_degree78.json` | 12 | 101 | 78 | Delivered literal; selected audits pass |
| Budget/centering `positive/eleven/...277.json` | 11 | 111 | 277 | Delivered literal; selected audits pass |
| Budget/centering `positive/twelve/equation.json` | 12 | 103 | 78 | Delivered literal; selected audits pass |
| Centered norms `positive11/...277.json` | 11 | 111 | 277 | Delivered literal; selected audits pass |
| Centered norms `positive12/equation.json` | 12 | 103 | 78 | Delivered literal; selected audits pass |
| Joint guards `pell/...277.json` | 11 | 111 | 277 | Delivered literal; selected audits pass |
| Joint guards `pell/...257.json` | 11 | 114 | 257 | Delivered literal; selected audits pass |
| Separate manuscript, twelve-variable section | 12 | 100 | 70 | No delivered JSON; independently materialized below |

The 111/277 point dominates the old source70 eleven-positive 113/325
point. The 114/257 point is a further degree/cost tradeoff; it does not
alone dominate 113/325, since it has one extra operation. The structural
101/78 point dominates the other two delivered twelve-positive 103/78
circuits. The materialized ordinary 100/70 manuscript point further
improves 101/78 in both measures.

All four packages use exactly the same **whole compact44 positive tuple**,
`beta=2^590069-1`, `K0=K`, `MC`, and already shifted `MF_source`.
The four decompressed hashes match source69's retained binding. No
source34/compact54 ports are interchanged and MF is not shifted twice.
This review authenticated the compressed/raw hashes and lengths, as well
as the actual inequalities `K0>=1`, `0<MC<beta`, `0<MF<2beta`.

## Eleven variables: why deleting q(q-1) is justified

The common 111/277 mechanism changes source70's strong ordinate from
`I=i q(q-1)c²` to `I=i c²`. Its three-root norm retains radicands

```text
Dtau=ell(ell+k)+1,
Df=1+Delta I²,
Dy=(QV²-1)/(Q-1), Q=Delta²I²,
V=Df(cT-R)-c.
```

The unconditional separation proof only needs `I>=c²`, which the smaller
ordinate still satisfies. In particular `1<Dtau<Df<Q`. Writing the
integer `b=cT-R`, one has V=-c for b=0, and `|V|>=Df-c>1` otherwise.
These bounds make the three radicands distinct and force one root to
dominate the sum of the other two. Thus no signed sum is zero. The octic
norm then yields a rational sum of three distinct radicals, and its exact
rational-extraction identity makes each root rational.

Rational-square integrality handles the first two roots. The former
prime-support argument for the third is replaced by source69's adjacent-
coefficient descent: for integer Q>1,V, every rational y satisfying
`QV²-(Q-1)y²=1` is integral. This is a universal descent on |V|, not a
bounded Pell search. It applies before transport positivity, q³|Y, or
index recovery, so deleting q(q-1) does not create a circular assumption.

The uncentered guard remains `L=3Df(cT+Rhat)` and satisfies
`L>sqrt(Df)+sqrt(Dy)`. For any signs recovered from the norm,
`r=n+L-f_signed-y_signed` is positive; the signed roots must be used
here. The inherited weighted carrier theorem then applies. Completeness
has the direct map `i_new=q(q-1)i_old`, preserving I and every downstream
register. This establishes a genuine witness-level reduction.

The degree audit includes the main-carrier degree-14 cancellation; mere
gate-degree propagation is insufficient. The norm has degree264 and the
main residual degree13. Their product has degree277. The displayed
coefficient `2^7*3^8*(3beta)^60` is nonzero independently of K0,MC,MF.
The independent modular univariate evaluation with **actual** ports also
has degree277. Budget/centering, centered-norms, and joint-guards ship
identical source arrays for this 111/277 circuit; structural round11 uses
a differently scheduled literal with the same arithmetic construction.

## Centered eleven-variable 114/257 endpoint

Joint guards' `pell/CENTERED_PROOF.md` uses

```text
B0=cT+Rhat, L=Df+B0,
hstar=4q Df+L, W=1+(q-1)hstar,
Zbar=M(ell+k+n+L+V)+(q-1)Y-q³W Bt.
```

The radical-separation/integrality argument is unchanged. The proof does
not assume the recovered transport gap is positive to derive C>0.
First `M|Zbar` yields `q³|Y` and `q-1|Bt`. Absolute main-root
classification suffices to obtain `c>8q⁹` even before C or R has its
desired sign bounds. The actual masks give the unconditional estimate
`|R|<Rhat`. They also give `y-|V|<B0`.

To bootstrap C>0, suppose C<=0 and put B=-Bt>0. The explicit identity
with `alpha=q-F-C` gives `R<qB+q⁴+q²`. For V>0, the centered gap
`L+V-f-y` is already positive, contradicting the signed-root sum. For
V<0, `R>=cT>=c>8q⁹` gives `R<2qB`; the gap is greater than
`-2Df R`, while `WB/(q-1)>4qDf B>2Df R`, again a contradiction.
V=0 is excluded unconditionally. Thus C>0 and then `V>1`.

Consequently `r=n+L+V-f_signed-y_signed>0`. For completeness the
canonical weighted source permits `r>L`; choosing
`n=r-L+f+(y-V)>0` supplies the centered norm. No new strong-index
congruence is imposed.

The exact inner cancellation is
`Jn=delta[z(z+2MV)-A-Bf]-M²(V²-1)`, with `z=Zbar-MV`.
It lowers the norm degree to244 and the final degree to257. Its selected
coefficient is `2^19*(3beta)^52`, independent of the other ports. Both
the centered algebra audit and this review's actual-port univariate
evaluation pass. The three extra gates are correctly reported.

## Twelve variables: normalized 101/78 and ordinary 100/70

Structural round11's delivered normalized 101/78 polynomial is **exactly
the same algebraic synthesis** independently reconstructed in
[short-unit-products](research/short-unit-products/README.md): source69's
rational two-coordinate merger with source73's adaptive
`U=q²Y`, `Dstar=U(X+ac)+H(U gamma+qXY-(k-R-1))`.
The qXY product shares E=XY. No novelty claim is appropriate for that
local reconstruction. Budget/centering and centered-norms instead use
`S=4qY,U=qS` and take 103 operations at the same degree78. Their
modulus recovery handles the possible common divisor three explicitly;
it never cancels H modulo U without justification.

The separate manuscript changes the merger's normalized strong norm to
the ordinary one. It sets `d=c⁴`, `Q=Delta(f²-1)`,
`AN=d h(n)+(1-Q)Q`, `N=AN²-d bn²Q`. Its root recovery gives
`(ic²)²=Delta(f²-1)` rather than `f²-Delta(ic²)²=1`.
The new degree/cost claim therefore needs an additional rank-size
argument, not just a formal substitution in a known polynomial.

The early adaptive carrier proves `q⁴|(k-R-1)` before either strong or
auxiliary recovery. Together with `k=2m1 (mod 4XY²)` it gives
`2m1=R+1 (mod q⁴)`. Since `0<R+1<q⁴`, the multiplier is nonnegative,
so `m1>=(R+1)/2>=24` and the main index p is larger. This implies
`c>(a+2)Delta²` before using the ordinary norm. The retained ordinary
strong-rank lemma then applies, and its signed auxiliary theorem recovers
p=R. No unjustified division of the recovered i by Delta is used.

The full argument and literal reconstruction are now in
[ordinary-unit-products](research/ordinary-unit-products/README.md).
The new JSON really has 100 live operations, residual degrees15,13,42,
and exact degree70 with coefficient `64(6beta)^18`. It passes separate
normal/optimized checks. Direct recovery of compact44's two extra
coordinates `o=f(cT-R)` and `j_source=(V+R)/c` binds it to that
archive's literal seven-equation positive kernel with the shifted z.
Canonical completeness replaces `i_normalized` by
`i_ordinary=Delta i_normalized`, takes `n=i_ordinary+u`, and preserves
the whole fixed tuple.

The manuscript's statements that a JSON graph and exact checker are
delivered cannot be verified from `report.zip`: it contains only one TeX
file and also includes references to other omitted sections. The circuit
just described is a **new local materialization**, not a replay of an
unshipped member. This is an artifact-completeness issue, rather than an
obstruction to the displayed twelve-variable mathematical construction.

## Evidence and boundaries

[PROPOSAL_REVIEW_WAVE11_POSITIVE.json](PROPOSAL_REVIEW_WAVE11_POSITIVE.json)
records archive pins, literal hashes and operation breakdowns, actual-port
univariate leading coefficients, whole-tuple hashes, and every selected
normal/optimized replay stage. Its independent interpreter is
[review_wave11_positive.py](tools/review_wave11_positive.py); it never
imports a builder or executes archive code. Selected authored scripts
were inspected first: their only subprocess in this scope reruns a Python
builder in a temporary directory. No `lean`, `lake`, dependency installer,
network command, or TeX build was invoked.

The degree specializations independently certify lower bounds; exact
upper bounds and nonzero fixed-slice coefficients come from the reviewed
symbolic cancellation arguments and exact algebra audits. Neither this
receipt nor a bounded test proves the universal Pell classification,
native tableau extraction, calibration of a whole tuple to K215, or the
object-language ZFC biconditional. The proposal proofs explicitly inherit
those ordinary interfaces and distinguish the unfinished formal endpoints.
