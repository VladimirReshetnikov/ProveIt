# Independent mathematical review

Final scope check: the compiled continuous-syntax kernel is single-sort.
The delivered README, theorem ledger, Lean README, and verification chapter
explicitly separate it from the many-sorted human proof and pending Lean
generalization. The final variational proof also explicitly clips rational
center approximations to `[0,1]` before applying the supporting-hat estimate.

Review scope: `work/analytic_topology.tex`, `work/category_models.tex`,
`paper/sections/03_function_spaces.tex`, and
`paper/sections/05_variational.tex` in the output package.
The reviewer read the definitions and arguments, checked the principal
constants independently, and examined choice, coding, and induction
boundaries. This is a mathematical review, not a claim that the full
manuscript has a completed `Prf PRAAx` formalization.

## Overall finding

The principal analytic estimates are sound after the explicit repairs
below. In particular:

* the clipped finite envelopes are always legal members of the shared
  bounded Lipschitz class;
* their approximation error and cardinality bounds are correct;
* uniform finite correspondence transport genuinely has no quantifier-rank
  error loss for the stated nonexpansive connective basis;
* the tent variational optimum is exactly `1/4`;
* the tent residual estimate is `D(f,t)^2 ≤ 2 J(f)`, and
  `κ(k)=2k+3` is a valid diameter modulus;
* the completion extension, residual recovery, contraction, and cube-root
  schedules have sufficient quantitative slack.

No hidden unbounded search or arbitrary infinite choice is needed in the
repaired versions. The finite arithmetic content can be organized under
quantifier-free induction with fixed program symbols. The manuscript
correctly retains semantic completion and the new compiled Lean kernel as
separate from yet-to-be-implemented object-theory derivations.

## Issues found and their repairs

### R1. Diagonal completion needed row regularity — repaired

The four-index inequality

`d(x[i,p],x[j,q]) ≤ eps(i)+eps(j)+eps(p)+eps(q)`

does not itself make `p ↦ x[i,p]` a name. In the rational line,
`x[i,p]=(-1)^p * 2^(-i)` satisfies this bound while every fixed row
oscillates. The theorem's reference to the completed value of the jth row
therefore originally lacked a hypothesis.

The author has now added that every row is a regular name. The diagonal
`z[n]=x[n+2,n+2]` and the claimed distance to the jth row then follow
exactly as written. The manuscript also now states represented completeness
for families supplied with joint names, avoiding countable representative
choice for arbitrary quotient-valued sequences.

### R2. Weighted gluing needed a sampled-domain guard — repaired

The denominator hypothesis `S ≥ δ` on an unspecified domain of interest
did not justify applying it to every sample of an arbitrary regular name.
A name of a point in a closed domain can have samples outside that domain.

The author has introduced a presented subdomain `D0 ⊆ D`, with all input
samples required to be valid codes of `D0`, and all analytic/denominator
contracts restricted to `D0`. The metric remains ambient so chart centers
may lie outside `D0`. The gluing theorem now applies to the represented
completion of `D0`. This supplies exactly the missing guard.

### R3. Function-space distances needed a named-distance transfer — repaired

The first continuous-model theorem used a rational metric and a decidable
exact comparison relation. Function-space centers have only rational
approximants to their supremum distance. They could not directly be used
as sorts under the original exact-metric interface.

The new named-distance lemma is correct. With

`u=U(h)`, `δ=2^(-u)`, `n,m ≥ u+2`,

query the distance to error `δ/8` and accept a pair when its rational
answer is at most `5δ/8`. A pair supplied by coverage has true distance at
most `δ/4`, so its sample is at most `3δ/8` and is accepted. Any accepted
pair has all-precision upper distance at most `3δ/4`. A free-parameter
pair within `δ/2` is also accepted. Thus the same atomic distortion estimate
and finite correspondence theorem apply.

The all-precision `Upper` conclusion follows by generalizing one arbitrary
distance precision after a coherence inequality. It is not an unbounded
induction formula. Relation construction and scanning remain decidable
rational operations. The corrected canonical mesh `U(p_k)+2` suffices.

### R4. The grid exponent s must be natural — repaired

An arbitrary integer `s` with `L ≤ 2^s` can be negative; then
`m_k=k+3+s` would not be a valid natural grid index for all k. The function
chapter now requires a natural `s`, which always exists and also handles
`L=0`.

### R5. Tarski–Vaught proof should avoid an unconstructed auxiliary infimum — repaired

The approximate-witness proof originally introduced `inf_A ψ^M`.
The hypothesis constructs the formula values over A and over M, but for a
fixed nonzero approximation error it does not automatically construct
this cross-interpretation infimum. An e-close perturbation of a located
family need not provide an infimum when only one fixed e is known.

The claim is correct with the following direct proof. Let

`LA = inf_{w∈A} ψ^A(w)` and `LM = inf_{b∈M} ψ^M(b)`

be the two already constructed values. If the subformula error is e,
then for every `w∈A`,

`LM ≤ ψ^M(w) ≤ ψ^A(w)+e`,

which gives `LM ≤ LA+e`. For every `b∈M`, the supplied witness list
contains `w` with `ψ^M(w) ≤ ψ^M(b)+τ`; hence

`LA ≤ ψ^A(w) ≤ ψ^M(w)+e ≤ ψ^M(b)+τ+e`.

The defining greatest-lower-bound property of LM yields
`LA ≤ LM+τ+e`. No third infimum is used. This proves the asserted
`q(φ)τ` budget. The dual proof handles suprema. The author has applied
this direct proof; it was re-read and confirmed in the revised chapter.

### R6. State the safe completed-parameter modulus explicitly — repaired

The formulas `U(k+ell)` and, for named distances, `U(k+ell)+1` are proved
for dense parameters. A closed-threshold modulus need not extend with
exactly the same threshold to an arbitrary metric completion: dense points
in two components can always have distance strictly greater than a threshold
while a pair of completion points attains that threshold.

The extension theorem already supplies safe shifts. One can state

* exact-distance completed modulus: `U(k+ell+2)+2`;
* named-distance completed modulus: `U(k+ell+2)+3`.

This does not change the finite cross-mesh theorem. It makes the
completed-parameter evaluation demand precise instead of relying on the
phrase “usual two-half error split.” The author has added these exact
moduli and explicit completed-input evaluation schedules. The two output
errors in those schedules are each at most `2^(-(k+1))`, as required.

### R7. c0 distance samples must be nonnegative absolute differences — repaired

The revised noncompact example correctly uses the unit ball of `c0` with
a supplied vanishing modulus, rather than assuming the supremum of an
arbitrary bounded real sequence. Its prefix calculation should explicitly
use nonnegative approximants to `|x_j-y_j|`.

One implementation is to approximate `x_j` and `y_j` each to error
`2^(-(k+3))`, then take the absolute difference. The error is at most
`2^(-(k+2))` and the resulting score is nonnegative. The tail is at most
`2^(-(k+1))`, and the claimed full-distance error follows. Without absolute
values the expression is the wrong distance; without nonnegative scores,
the displayed `2^(-(k+1))` bound can lose an additional sampling error.
The author has made precisely this sampling construction explicit; the
revised error bound is correct.

### R8. Computability of extrema needs the objective evaluator and modulus — repaired

Two function-space sentences should retain their input data explicitly.
Qualitative continuity of a functional does not give a PR evaluator or a
PR uniform-continuity modulus. Even a constant functional can have a
noncomputable constant value. A dense net and a modulus alone do not
determine its values on the net.

The remark on all semantic functions should say: given an evaluator for
the functional on the coded centers, its uniform modulus and the explicit
nets suffice to compute its extremal value. The paragraph after uniform
completion should restrict its PR-extremizer claim to a functional supplied
with a PR evaluator and a PR uniform-continuity modulus. These are exactly
the intended framework hypotheses; the change avoids an unqualified
computability assertion. Root has applied both edits, and they were
re-read in the output chapter.

## Independent checks of the main quantitative claims

### Function-space envelopes and membership

Every cone `q_a + L*d(x,a)` is L-Lipschitz; finite minimum preserves L,
and clipping is nonexpansive. Thus every table produces a legal function,
including tables inconsistent with any exact interpolation. If every
entry differs from `f(a)` by at most δ, then for all a,

`q_a+L*d(x,a) ≥ f(x)-δ`.

A covering center within h gives the upper bound
`f(x)+δ+2Lh`. Clipping fixes f(x), so it cannot enlarge the error.
There is no hidden extension theorem or feasibility test in membership.

The proposed parameters give `2L*2^(-m_k) ≤ δ_k` and hence error
`2δ_k=2^(-(k+1))`. The number of tables is exactly

`(2M*2^(k+2)+1)^((2^(k+3+s)+1)^d)`.

All exponents and loop bounds are primitive recursive with the displayed
numeric parameters variable. The center evaluator interprets a fixed
finite table format, not arbitrary PR program codes.

The supremum-distance estimate `2η+2Lh` is also correct: pointwise
sampling contributes `2η`, and `|f-g|` is `2L`-Lipschitz. This construction
produces the distance as a name without presupposing an arbitrary supremum
principle. If the model-theory interface retains diameter ≤1, explicitly
rescale this metric by the known positive bound `2M`, or note that the
proofs of the interface do not actually use that diameter restriction.

The uniform completion construction uses a joint sequence evaluator and
the supplied Cauchy modulus. It defines the output value at each input
by a specified name, rather than choosing pointwise limits independently.
For currying, an explicit name in the function-space representation can
be obtained by applying the previously proved table-selector construction
to the section `x ↦ H(a,x)` at every requested precision.

### Tent variational problem

The retraction `Rf=max(-t,min(t,f))` is correct. Each of `-t,t,f` is
1-Lipschitz, their lattice min/max preserves this constant, and the endpoint
values become exactly zero. Pointwise clipping into the same interval
shows `D(Rf,Rg)≤D(f,g)`, so the image net supplies an actual net of the
anchored class. No general closed-subset effective-compactness principle
is used.

The finite sum identity is valid, including n=1:

`sum_{j=0}^{2n-1} min(j,2n-j) = n^2`.

Thus the even left Riemann sums of t equal `1/4` exactly. Every admissible
f is pointwise ≤t, so the displayed upper bound and sampled error budget
follow. The `1/N` integration error is conservative and valid for a
1-Lipschitz function.

For the residual, `g=t-f` is nonnegative and 2-Lipschitz, with g(0)=g(1)=0.
If g(x)=a, then `a≤2*min(x,1-x)`, so the full supporting triangle of
`max(0,a-2|x-y|)` lies inside [0,1]. Its area is `a^2/2`, yielding
`g(x)^2≤2J(f)`. No maximizer of g is needed to pass to supremum distance.
If each residual is at most `2^(-(2k+3))`, each distance to t is at most
`2^(-(k+1))`, and their sum is at most `2^(-k)`. The proposed κ is correct.

For an especially explicit finite implementation, take a rational point r
and a rational lower height `A=max(0,sample(g,r)-η)`. The endpoint/variation
contracts give `A≤g(r)` and `A≤2*min(r,1-r)`. The rational hat
`max(0,A-2|r-y|)` has rational breakpoints and integral `A^2/2`; its
left-sum error is at most `2/N`. Comparing finite sums with those of g,
then decreasing η and increasing N, proves the same residual estimate.
This is a useful expanded proof path, not a correction to the mathematical
estimate.

### Completion, gluing, and residual constants

For extension, `h(n)=μ(n+2)+2` makes two input errors at later indices
at most half the input tolerance. The transferred output is regular.
With input distance `eps(μ(k+2)+2)`, three input terms sum to at most
`3/4` of the input tolerance. The extension modulus and uniqueness proof
therefore have sufficient slack.

The gluing constant `L+2NM/δ` is valid even when one local weight vanishes:
the one active term is bounded by `M*|α-β|`, so no inactive local contract
is silently used. The named-distance inner weights lose at most `2eps(t)`
each. The quoted perturbation bound `8MN*eps(t)/δ` is conservative;
the positivity condition on the approximate denominator suffices.

The residual recovery indices bound both witness residuals at the required
diameter threshold, and continuity identifies the represented zero.
The contraction schedule `F^(H(n+B))(x0)` is correct because `q^H≤1/2`.
The real cube-root construction has residual error

`6*2^(-(n+5))+2^(-(n+4)) = 2^(-(n+2))`.

Its separation inequality has the correct factor 4, and hence
`κ(k)=3k+3` and inverse modulus `3k+2` are valid. No exact real sign
selection is used.

## Formalization and strength boundary

The new compiled Lean formula theorem is exactly the finite semantic result
stated in the chapter. It does not silently supply new `Prf PRAAx` proof
terms. For fixed syntax, the proposed object translation uses actual PR
folds and externally generated proof trees. Variable-length invariants
are bounded and can be Booleanized; arbitrary all-precision hypotheses
are instantiated as open premises rather than inserted into induction.

The observable-quotient proposition is sound with its supplied section;
the section provides the only representatives needed. The approximate
Tarski–Vaught theorem is a conditional transport theorem, not a method
for manufacturing elementary substructures. The formalization status and
these retained obligations should remain explicit in the final summary.

## Review closeout

All eight identified repairs are present in the revised source chapters
and output function-space chapter. The variational chapter now expands
the finite rational triangular-hat argument, including exact trapezoid
areas and a controlled passage from represented centers/heights. The
review found no remaining substantive flaw in the claims within its
scope. As usual, any rational approximation to a point of `[0,1]` used
as a function argument is taken in `[0,1]` (clip it if necessary).

No further optional numerical tests were run. The original checked Lean
kernel and its precise semantic/object-theory distinction remain
unchanged by these prose repairs.
