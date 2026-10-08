> Editorial status: this is the independent audit record. The reported corrections
> were incorporated into the distributed article; the combined article is the
> authoritative statement of the final hypotheses and implementation scope.

# Independent final mathematics audit

Reviewed 8 October 2026. Scope: `research_notes/montesinos.tex`,
`research_notes/math_inspiration/rational_continuation_rank.tex`,
`unknot_arithmetic_continuations/fast/fastunknot/rational.py`,
`unknot_arithmetic_continuations/fast/fastunknot/tangle_obstruction.py`,
the relevant `Diagram.from_pd` validation, and the benchmark protocol/results.
This review did not modify implementation or article sources.

## Verdict

**No substantive mathematical soundness blocker found**, provided the final
article preserves the input-model and complexity qualifications below. The
structured Montesinos classifier, closure-independent local obstruction,
separating-disk certificate, rational connection-matrix construction, and
bounded-description search are coherent. Their combination does not establish
general quasi-polynomial unknot recognition.

The source fragment permits more local patterns than the shipping implementation.
The article must retain the implementation's stricter scope: initial `e=0`,
each original summand has reduced finite denominator greater than one, connected
crossing shadow, exactly two open strands, and four distinct edges genuinely
leaving the selected crossings. This restriction loses some valid witnesses
but does not admit false positive certificates.

## 1. Production arithmetic: the quadratic bit bound is justified

Define binary source length `B` to include the coefficient count, separators,
signs, and at least one bit per coefficient, including zero. For a coefficient
`a`, charge `b(a) = 1 + ceil(log2(1+|a|))`. A continued-fraction block with total
charge `B_i` has every primitive projective entry of `O(B_i)` bits. Its
recurrence multiplies an entry of accumulated length by the next coefficient;
the aggregate schoolbook cost is bounded by the sum of products of coefficient
charges, hence `O(B_i^2)`, including additions and sign normalization.
Summing over blocks gives `O(B^2)`. No gcd computation is required: all CF
matrices are unimodular, so their first columns are primitive even when an
intermediate projective denominator is zero. A final zero denominator is
correctly rejected.

Each `divmod(p,q)` costs `O(B_i^2)` with schoolbook division. The repeated
normalization additions cost at most `O(B^2)`. Let `c_i` be the bit length of
the normalized denominator `alpha_i`; then `sum c_i = O(B)`. For
`Q_j = product_{i<=j} alpha_i`, the stored numerator is

`D_j = normalized_e * Q_j + sum_{i<=j} beta_i * Q_j/alpha_i`.

Since `0 < beta_i < alpha_i`, its length is
`O(bit_length(normalized_e) + log(j+1) + sum_{i<=j} c_i) = O(B)`.
The accumulator multiplications have aggregate cost
`O(sum_j c_j * (B + sum_{i<j} c_i)) = O(B^2)`.
Computing the expansion-size statistic, coefficient count, stored-state bit
statistic, and constant-many hexadecimal encodings does not exceed this bound.
The generated certificate has `O(B)` encoded bits. Negative coefficients and
cancellation do not invalidate the upper bound.

**Terminology correction:** `max_entry_bits` measures the maximum of the
*tracked CF entries, normalization states, and accumulator states*. It is not
the maximum length of every temporary multiplication result, and is not a
peak-memory measurement. Concrete checked example:

```python
montesinos_certificate(-2, [[0, 1, 3, 2]])
# slope 7/9, signed determinant -11, max_entry_bits == 4
# temporary numerator*alpha == -18 has 5 bits
```

The independent replay accepts this certificate, as intended. All actual
temporaries still have `O(B)` bits.

## 2. Arithmetic replay: cubic is a safe bound

The verifier's forward CF matrices cost `O(B^2)`. Its independent full-product
homology formula costs at most `O(B^2)`. Replaying the reported maximum state
size recomputes a product sum for every prefix. With
`S_i = sum_{j<=i} c_j`, the `i`th prefix costs
`O(S_i^2 + bit_length(normalized_e)*S_i)`; summing over at most `O(B)` prefixes
gives `O(B^3)`. This amortized estimate is necessary: treating every division
as an unrelated full-size `O(B^2)` operation would give an unnecessarily loose
quartic estimate.

For externally encoded certificates, include the cost of reading their encoded
length, or restrict to the generated `O(B)` certificate schema. The replay is
independent in its arithmetic recurrence, not a separate formal proof checker:
it shares schema/status construction and trusts the cited topology.

## 3. Topology and exceptional fibres

The whole-source arithmetic keeps each rational summand separate. It correctly
uses the unreduced common-denominator numerator; reducing their rational sum
would be wrong. Absorbing denominator-one terms and transferring integral
parts preserves the standard Montesinos link. Remaining denominators really
are exceptional orders: each is at least two and coprime to its numerator.

For at least three exceptional fibres, the closed-cover group surjects onto
the stated triangle group after killing the regular fibre and the other
exceptional generators. The explicit `PSL_2(C)` matrices provide a nontrivial
representation for every triple of orders at least two; no finite-group
classification, factoring oracle, or cyclotomic-field computation is needed.
For at most two fibres, the numerator closure is a rational link; the open
horizontal sum itself need not be a rational tangle. The determinant-one
acceptance branch is therefore justified by rational-link classification.

The code's odd-determinant component test is equivalent to the fragment's
explicit component formula: two or more even denominators force an even
determinant; exactly one forces an odd determinant; with none, parity is
`e + sum beta_i`. Consequently odd determinant is exactly the one-component
condition on this source class.

The local theorem matches [Nogueira–Salgueiro, Theorem 4.9(a)](https://arxiv.org/html/2110.15645v1),
including `q_i>1` and the genuine two-string hypothesis. Its use of rational
complements is justified by Proposition 4.4 after proving essentiality via the
injective boundary torus group. The fragment correctly treats the infinite
complement separately using denominator closure, whose determinant is the
product of the denominators. A successful local congruence supplies no positive
verdict for an arbitrary exterior.

## 4. The common-face disk and forced matching

The disk proof is valid. The matched connected shadow inherits its plane
rotation system from the validated whole diagram. Every incident dart at an
image crossing is accounted for. Thus every component of the remaining
diagram attaches through a port, and all such components lie in the single
certified port face. Filling the other complementary disks of a regular
neighborhood gives a genuine disk intersecting the knot precisely at the four
ports. Over/under data then identifies the tangle in the associated ball.

The implementation additionally requires every port edge to lead to an
unselected crossing, excluding cases with two ports on one outside arc. This
is conservative and sound. Connectedness and the common-face test must not be
replaced by a bare four-edge-cut test.

After template compilation, an image and an even cyclic offset of the root
crossing force every other image and offset. There are at most `2n` trials in
the implementation, each taking `O(k)` propagation/checking work. Public
revalidation includes edge-label sorting, giving the stated
`O(n log n + nk)` word bound after compilation. A deterministic indexed-array
implementation realizes the abstract word bound without hash-table assumptions.
For arbitrary source syntax, add parsing/CF/compilation costs: arbitrarily many
zero coefficients can describe a fixed-size crossing pattern. For a fixed
catalogue these source costs are constants.

The default 100,000-crossing expansion cap is an implementation resource policy.
The theoretical bounded-description enumerator must use an uncapped compiler
or explicitly report a resource limit; the capped API is not complete for all
diagram sizes. The abstract `(n+2)^{O(h)}` source count and bit bound remain
valid under the narrower implemented source grammar and distinct-cut-edge
condition. The `h=O(log n)` conclusion concerns literal witness discovery only.

## 5. Rational continuation matrix

The disjoint-cone argument, primitivity, endpoint parity, and determinant
separation check out. The primitive base columns `(1,1)` and `(3,2)` have
determinant `-1`; the generators are unimodular and congruent to identity
modulo two. Every cross closure is a knot. Off-diagonal determinants have
absolute value greater than one, and the stronger bounds 19/21 are correctly
expanded. The gluing rule agrees with
[Kauffman–Lambropoulou, Theorem 5](https://arxiv.org/pdf/math/0601525).

The identity submatrix therefore has rank `2^m` over every field. This is a
lower bound for exact Boolean linear summaries, not for arbitrary arithmetic
summaries or algorithm runtime. The signed gluing matrix has rank at most two
over the rationals, and the nonlinear test `|D|=1` explains the distinction.
The `O(m^2)` schoolbook time and `O(m)` arithmetic storage bounds are sound.
For uniform statements including `m=0`, write `O(m+1)` and `O((m+1)^2)`.
Minor TeX typo: `\mathbb R_{>0}^{,2}` should be `\mathbb R_{>0}^{2}`.

## 6. Benchmark interpretation

The recorded protocol is a paired warm-process ablation, with fresh diagram
objects, and correctly withholds speedup ratios when the baseline returns
`UNKNOWN`. The 44- and 52-crossing diagonal examples are censored by the object
budget, not established multi-second baseline solves. Do not turn the cap into
a completed-solve speedup.

The large structured-source ratios are recognition-stage ratios with the same
checked source construction outside both timers. Construction already evaluates
source arithmetic. The separately measured new end-to-end times include PD
construction and are substantially larger; for example the 575-crossing case
has roughly 40 microseconds recognition versus 4.97 milliseconds end to end.
The article should show this distinction prominently. These selected families
demonstrate value from retained certified structure, not general average-case
performance or automatically discovered Montesinos decompositions.

The local branch has mixed results: the planted double-three example improves
modestly, the planted Alexander-one example is slower than the existing
Rasmussen rejection, and the catalogue controls all pay overhead. The opt-in
policy is justified. Planted experiments supply the pattern source; they test
map discovery and verification, not exhaustive CF-source discovery. Huge
binary-coefficient timings concern compressed arithmetic without PD expansion,
and provide no empirical proof of a complexity exponent.

## 7. Additional checkpoint lower bound: approved

The later fragment
`research_notes/math_inspiration/unknot_checkpoint_lower_bound.tex` was also
reviewed. **Both the ungraded closure-functor bound and the stronger graded
bound `M(C_k) >= p_k + q_k` are sound in their stated categories.** No software
tests were rerun for this review.

The reduced closure functor is well defined on the unpointed tangle category:
the basepoint is placed on a fixed exterior closure arc, so its product track
lies on every closed cobordism. Multiplication by `X` commutes with every such
map, making reduction by `A/(X)` functorial. Additivity, rather than exactness,
is sufficient to preserve chain homotopy equations. A circle-free matching on
`2r` endpoints closes to at most `r` circles and hence at most `2^(r-1)` reduced
generators. This proves the weaker bound independently of a grading assumption
on the chosen homotopy representative.

For the stronger bound, a shifted matching whose closure has `c` circles has
reduced graded dimension equal, up to a monomial, to
`(z + z^(-1))^(c-1)`. At `z=i`, it vanishes for `c>1` and has absolute value
one for `c=1`. Each summand also contributes its homological sign, again a
unit-modulus factor. Consequently the absolute reduced Jones value is bounded
by the total number of summands whose closure is one circle. This is an
integer graded Euler-characteristic argument evaluated in the complex numbers;
it works over any coefficient field and does not require Khovanov thinness.

For four endpoints, numerator closure kills the horizontal matching's
contribution at `z=i` and isolates the vertical matching; denominator closure
does the reverse. The primitive positive columns `(p_k,q_k)` are odd in both
coordinates, so both test closures are rational knots with determinants
`p_k` and `q_k`. Thus `M_V >= p_k`, `M_H >= q_k`, and their sum gives the
claimed bound. The fixed exterior marking introduces no dependence on which
circle is reduced: after normalization, any marked `c`-circle object has the
same reduced graded dimension.

There is a subtle orientation point, but the fragment's final qualification
handles it correctly: one orientation of the two strands of `P_k` need not
extend to both closures. Start with the orientation-free bracket complex;
reorienting strands changes only its global homological/quantum normalization
shifts. Each chosen closure therefore computes its normalized reduced Jones
polynomial up to a global monomial/sign of absolute value one at `z=i`.
The two estimates apply to the same matching multiplicities.

The Pell recurrence, initial values, closed expressions, and exact displayed
crossing count `8k+4` check out. The actual closure `K_k` is an unknot because
its primitive gluing determinant is `-1`. In particular, `p_k+q_k` gives
`10, 58, 338, 1970` for `k=1,2,3,4`. Agreement with the recorded benchmark
counts is an observation, not proof of an upper bound, identification of every
measured checkpoint, or an order-independent lower bound.

The conclusion requires an expanded complex made from actual shifted,
circle-free crossingless matchings and a grading-preserving homotopy
equivalence for the stronger estimate. It does not apply automatically to a
deformed specialization whose simplification cannot be specialized back to
ordinary Khovanov theory, a different basis of compressed objects, arbitrary
scan orders, or compact binary multiplicities. The fragment makes the relevant
expanded-basis and prescribed-checkpoint restrictions explicit.

## Remaining release conditions

1. Preserve the production/verifier/statistic terminology and source-cost
   qualifications above.
2. Make the fragment-versus-implementation local input restrictions explicit.
3. Keep fixed-catalogue implementation, theoretical exhaustive discovery, and
   general unknot recognition as distinct scope claims.
4. Describe the benchmarks as selected-family ablations and report the local
   regressions alongside the improvements.

With those editorial conditions, I recommend inclusion of the reviewed results.
