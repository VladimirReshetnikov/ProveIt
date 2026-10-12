# Exact maximal support before normal-sector enumeration

This optional module identifies every quadrilateral coordinate that is zero
throughout a supplied compatible matching cone. It returns a complete support
certificate when successful. Existing default recognition and sector-discovery
behavior is unchanged.

## Mathematical contract

For an exact rational matrix `A`, consider `C = {x >= 0 : A x = 0}`. The
certificate consists of rational vectors `x`, `y`, and `lambda` satisfying

\[
Ax=0,\qquad y=A^T\lambda,\qquad x,y\ge0,\qquad x+y\ge\mathbf1.
\]

Because `x` and `y` are orthogonal, their supports partition the coordinates.
Every feasible vector vanishes on the support of `y`, and the supplied `x`
simultaneously witnesses every coordinate in the complementary support. Thus
the retained support is maximal, not merely a sound subset of coordinate-zero
implications.

The feasibility system has no guessed coefficient bound or big-M constant.
Splitting `lambda` into positive and negative parts makes it an ordinary LP.
Existence follows from the coordinate alternatives for a rational subspace and
its orthogonal complement. After restricting to retained coordinates, `x` is
strictly positive, so the matching nullspace equals the span of the feasible
cone. This is the dimension relevant to subsequent ray enumeration.

## APIs

From `Topology/UnknotRecognition/fast/`:

```python
from fastunknot.sector_maximal_support import (
    certify_nonnegative_kernel_support,
    certify_maximal_support,
    discover_in_maximal_support_sector,
)
from fastunknot.sector_maximal_support_verify import (
    verify_nonnegative_kernel_support_certificate,
    verify_maximal_support_certificate,
)

result = certify_nonnegative_kernel_support([[1, 1, 0]])
assert result["status"] == "COMPLETE"
assert result["retained_indices"] == [2]
assert verify_nonnegative_kernel_support_certificate(
    [[1, 1, 0]], result["certificate"]
)

# `triangulation` and `allowed_types` use the existing source-sector formats.
support = certify_maximal_support(triangulation, allowed_types)
if support["status"] == "COMPLETE":
    assert verify_maximal_support_certificate(
        triangulation, allowed_types, support["certificate"]
    )

answer = discover_in_maximal_support_sector(
    triangulation, allowed_types, phase="standard", max_bases=1000
)
```

The generic input matrix accepts only integers and `fractions.Fraction`
coefficients. For a matrix with no rows, use `width=k` to specify its width.
Returned supports are indices in the original column order. Source supports
are canonically sorted by tetrahedron/type, just as in the existing builder.

`certify_maximal_support` accepts an optional reusable `PreparedSectorSource`
through `source=`. Its existing read-only-source contract applies. The source
hash must match the requested triangulation. The certificate producer still
pays for independent source replay before returning success.

## Solver behavior and complexity limits

`solver="auto"` first asks optional SciPy/HiGHS for a floating-point proposal.
It infers a possible support partition, imposes its zero coordinates in exact
rational subspaces, reconstructs positive primal and dual vectors there, and
checks all equations and signs exactly. A tolerance or solver success flag is
never accepted as a proof.

If that path does not yield an exact witness, the optional SymPy rational
simplex is tried. Its output is independently checked as well. Set
`solver="scipy"` or `solver="sympy"` to use only one backend. Elementary empty,
zero-kernel, positive-unit-vector and one-dimensional cases need no LP backend.
Dependencies are imported only when required.

Missing dependencies, a rejected numerical proposal, or solver failure yields
`INCONCLUSIVE` without a support certificate. The opt-in discovery wrapper
then resumes the existing complete discovery path on the original sector. It
never deletes a coordinate on the basis of a failed solve.

**The implementation does not establish a polynomial worst-case bound for its
LP backends.** The mathematical polynomial-preprocessing theorem requires a
polynomial-time rational LP algorithm. HiGHS and SymPy's simplex are practical
search backends here; exact verification guarantees correctness of accepted
results, not a polynomial search bound. Neither this local theorem nor the
implementation supplies a complete quasi-polynomial family of unknot sectors.

The `check` callback runs throughout this module's own algebra, rebuilding,
and replay, including callbacks with a false Boolean value. Third-party LP
calls cannot invoke it internally: it is called immediately before and after
each solve. A callback raised after a solve prevents publication of any result.
There is no hard wall-time or simplex-iteration allowance in this interface.
Applications requiring such an external deadline should isolate the entire
query in a cancellable worker process. Existing `max_bases` and
`max_orbit_cycles` in the discovery adapter retain their established meanings;
they do not count LP arithmetic.

## Independent certificates and original-sector scope

`rational-kernel-maximal-support-v1` stores an input matrix digest, rational
primal/dual vectors, original-row multipliers, and the retained index list.
The checker performs only exact products, comparisons, and digest checks. It
imports neither elimination nor a producer or solver. Reordering matrix rows
requires reissued multiplier provenance and a new digest.

`normal-sector-maximal-support-v1` stores a source triangulation digest, the
original allowed support, an actual integral normal vector, one rational
combination of source matching rows, and the retained indices. The checker
validates the primal coordinates directly on the source. The dual combination
must cancel every triangle coefficient and satisfy the complementary support
conditions on all allowed quad types. Coefficients on nonallowed types are
unrestricted because those coordinates are zero in the requested sector.
The checker shares only the existing geometry validator and integer codec;
it imports no sector contraction, potential builder, nullspace routine or LP.

This proves maximal quadrilateral support. When the retained support is empty,
the standard normal cone can still contain pure vertex links; the conclusion
concerns non-link rays. No support certificate by itself asserts an essential
disk, an authenticated diagram exterior, or unknotness.

The discovery wrapper restores original coordinate widths in exhaustion
proofs and compiles the dual consequence into the already-supported
`normal-sector-matching-support-v1` annotation. Ordinary positive witnesses
also retain the original allowed list. The existing independent
`verify_sector_witness` and `verify_sector_exhaustion` accept these discovery
proofs unchanged. The separate full support certificate appears as
`answer["maximal_support_certificate"]`, including when later ray discovery is
capped and returns `INCONCLUSIVE`.

## Reproduction and evidence

```bash
python -m pytest tests/test_sector_maximal_support.py -q
python maximal_support_research.py --output maximal_support_results.json --repeats 3
python maximal_support_geometric_search.py \
  --output maximal_support_geometric_search.json --seconds 180 --sectors 128
python maximal_support_benchmark.py \
  --output maximal_support_final_benchmark.json --repeats 9
```

The first research script uses the existing
`../reports/57/results/discovery_corpus.json`. Its abstract family is

\[
p_i+z_i-z_{i+1\pmod m}=0\quad(0\le i<m),
\]

with optional extra free variables. A nonzero nonnegative row-space vector
requires all `m` RREF rows, so every one-/two-row propagation rule misses its
forced `p` coordinates for `m >= 3`. Maximal-support certification reduces raw
dimension `m+s-1` to feasible dimension `s`. These are abstract rational cones;
the script makes no claim that this entire family is realized by normal
matching equations of knot exteriors.

The maintained real-source corpus audit checks all 188 selected sectors with
raw dimension above three against its archived complete standard vertices.
The initial run agreed in every case and reduced dimension in 24 cases, but
found no extra zeros beyond the incumbent two-row closure. Its five pilot
complete-query timing comparisons were slower with the new opt-in stage.
The three-repeat pilot is evidence about overhead, not a robust speed claim.

The second script performs a separate bounded search in larger layered,
capped, and Pachner-modified solid tori, preserving its seed, actual source
pairings, sampled supports, and any discovered counterexample to pair closure.
The initial fixed-row search found a genuine 36-tetrahedron fixture after
2,187 sectors. One incumbent pass forced 22 coordinates; the complete support
proof forces 23. However, both reduced kernels have matching dimension five,
and rerunning pair closure after recompilation finds the remaining zero.
The preserved fixture and its regression test explicitly check this limit.

With `--iterate-incumbent`, the script repeats RREF and pair closure after
each restriction before comparing against the complete LP. A second search
completed all 4,864 scheduled sectors in 38 sources, including raw dimensions
up to ten, and found no additional zero missed by that iterated procedure.
This is a negative bounded experiment, not a completeness theorem for
iterated pair closure on normal matching systems. The abstract cyclic
obstruction remains a proof that such completeness fails for general rational
matrices, even when the initial matrix is already in RREF and no first
coordinate can be removed.

The final isolated benchmark uses nine paired repetitions with shuffled arm
order, both fresh and shared prepared sources, and an identical-incumbent
control. On the preserved 36-tetrahedron example, the median paired new/old
time ratios were **0.604** with fresh preparation and **0.573** with a shared
prepared source; the identical-code control ratio was **1.002**. Both methods
began 1,835 candidate bases and processed the same 31 combined Q/standard ray
records. This is a measured reduction of complete query cost without a
matching-dimension or enumeration-exponent improvement on that fixture.
All five smaller maintained-source cases had paired ratios above one. Their
millisecond timings also showed more variability in identical-code controls.

The benchmark JSON retains every raw sample, paired ratio, ratio of medians,
trial order and source identity. The median of paired ratios need not equal
the quotient of the two timing medians. Extra independent full-exhaustion
replay after the timed trials is explicitly excluded; verification performed
inside each queried API remains included. These results support keeping the
LP stage opt-in and do not recommend changing the default policy.
