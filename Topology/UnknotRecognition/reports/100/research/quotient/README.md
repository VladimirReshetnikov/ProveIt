# Exact certificates for a relative homology quotient

This research artifact implements an exact algebraic alternative. Its input is
a finite chain-pair fragment over the integers. Its output either proves that a
candidate relative cycle belongs to the rational image of the bundle cycles, or
proves that it lies outside that image. Both kinds of certificate use integers.

`produce.py` uses Python's standard-library `Fraction` and Gaussian elimination
with row provenance. `verify.py` independently verifies the result using only
strict integer type checks, matrix products, and equalities. The verifier does
not import or call the producer and does not perform elimination.

## Scope

The source-to-chain compiler is **unimplemented**. The included examples and
random tests are algebraic chain-complex instances, not authenticated knot
exteriors, bundles, normal surfaces, or measured improvements in unknot
recognition. A geometric application must authenticate all those objects and
the actual inclusion of pairs before interpreting an algebraic verdict as a
statement about a normal cut.

In particular, `INSIDE_BUNDLE_IMAGE` does not mean that a cut has zero quadratic
defect. It means the sufficient obstruction for strict progress does not apply.

## Input contract

The JSON object has exactly these fields:

```json
{
  "schema": "relative-chain-pair-v1",
  "dims": {"c1": 0, "c2": 1, "c3": 0, "e1": 1, "e2": 1},
  "d2": [],
  "d3": [[]],
  "e2": [[3]],
  "j1": [],
  "j2": [[2]],
  "s": [1]
}
```

The dimensions describe `d2:C2→C1`, `d3:C3→C2`, `e2:E2→E1`,
`j1:E1→C1`, and `j2:E2→C2`. Matrix dimensions are explicit, including when
there are zero rows or zero columns. Every number must be an integer; booleans,
floating-point numbers, and numeric strings are rejected.

The following exact identities are checked before producing or verifying a
certificate:

\[
d_2d_3=0,\qquad d_2j_2=j_1e_2,\qquad d_2s=0.
\]

These identities authenticate the algebraic fragment. They do not authenticate
its geometric origin. No differential on `E3` is needed to compute the image
of all bundle 2-cycles modulo `C`-boundaries; a geometric chain map must, of
course, also respect any higher differentials in its full model.

## Certificates

The producer solves

\[
\begin{pmatrix}d_3&j_2\\0&e_2\end{pmatrix}
\begin{pmatrix}a\\b\end{pmatrix}=
\begin{pmatrix}s\\0\end{pmatrix}.
\]

If consistent, it returns integer vectors `a,b` and a positive integer `q`
such that

\[
q s=d_3a+j_2b,\qquad e_2b=0.
\]

The verdict is `INSIDE_BUNDLE_IMAGE`. The factor `q` is necessary because the
question is membership over the rationals: for example, `s=[1]` and `j2=[[2]]`
have a valid support certificate with `q=2,b=[1]`.

If inconsistent, row provenance supplies integer rows `Y,U` and `q>0` with

\[
Yd_3=0,\qquad Yj_2=Ue_2,\qquad Ys=q.
\]

The verdict is `OUTSIDE_BUNDLE_IMAGE`. The restriction identity annihilates
every bundle cycle. Verification therefore does not need to trust an externally
supplied list that purports to be a complete cycle basis.

The two certificate types cannot both hold: applying `Y` to a support identity
would give a positive integer equal to zero. Finite-dimensional linear algebra
proves one always exists for a valid input. Certificates bind to the canonical
JSON input through its SHA-256 digest. This prevents accidental use with a
different instance; it is not a substitute for geometric authentication.

## Run

From this directory:

```bash
python produce.py examples/outside.json -o examples/outside.certificate.json
python verify.py examples/outside.json examples/outside.certificate.json
python -m unittest -v test_quotient.py
```

The producer and verifier require Python 3.10 or later and have no third-party
runtime dependencies. Tests additionally compare 250 deterministic random
instances with independent SymPy rank computations when SymPy is available.
Other tests cover empty dimensions, nonzero commuting squares, rational-only
support, nonunit dual evaluation, large integers, scaling, invalid chain
identities, stale input binding, hostile mutations, and command-line round trips.
One command-line round trip uses a 16384-bit input coefficient and the same
16384-bit support denominator, with the explicit setting described below.

### Very large decimal integers

The quotient wire format uses JSON decimal integers. CPython normally limits
conversion between integers and decimal strings to 4300 digits; its default
configuration can therefore reject an otherwise valid input or certificate
before the algebraic computation or during serialization. For trusted research
inputs exceeding that limit, launch **both** commands with the setting enabled:

```bash
PYTHONINTMAXSTRDIGITS=0 python produce.py input.json -o certificate.json
PYTHONINTMAXSTRDIGITS=0 python verify.py input.json certificate.json
```

This launch setting is exercised by the 16384-bit subprocess test. Direct API
callers have the same configuration requirement when the input digest converts
large integers to JSON. The quotient format does not use the raw-cut artifact's
hexadecimal integer codec. The configuration is documented in the
[Python integer string conversion documentation](https://docs.python.org/3/library/stdtypes.html#configuring-the-limit).

## Geometric theorem behind the intended interface

For an authenticated admissible handle structure `H`, let `B` be its interior
parallelity bundle and `A` its horizontal boundary embedded in `∂M`. This
embedding is an explicit hypothesis; having no 3-handles is a sufficient
condition. A general handle structure can have horizontal faces incident
to 3-handles. The conservative alternative `A = B ∩ ∂M` always defines
a map of pairs and gives the same sufficient implication below. If an
authenticated connected oriented normal surface `S` has class outside

\[
\operatorname{im}\bigl(H_2(B,A;\mathbb Q)\to H_2(M,\partial M;\mathbb Q)\bigr),
\]

then Lackenby's equality case for the quadratic complexity implies strict
decrease. Index conservation gives the more precise raw-cut identity

\[
c_q(H)-c_q(H\backslash\!\backslash S)
=2\sum_H\sum_{a<b}I(H_a)I(H_b)\ge2.
\]

All raw child 0-handles are included. Subsequent cleanup retains the lower bound
only when its nonincrease of `q` is separately established; the raw identity
must not be applied unchanged to an already reduced child inventory.

The separating functional belongs to `H²(M,∂M;Q)` and is dual to an absolute
`H₁(M;Q)` cycle. The **surface class**, rather than that functional, corresponds
to `H¹(M;Q)` under Poincaré–Lefschetz duality. This distinction matters for the
future prescribed-class normal-surface constructor.

Source: Marc Lackenby, *Incompressible surfaces, hierarchies and unknot
recognition*, arXiv:2607.23350v1, Definitions 5.1 and 5.6–5.8, Lemmas 5.2 and
5.5, Proposition 5.9, and the cocycle construction in Theorem 6.2.
<https://arxiv.org/html/2607.23350v1>

This artifact establishes no quasi-polynomial bound for the complete unknot
recognition algorithm. Its polynomial cost is measured in the declared chain
ranks plus the explicit matrix-entry bit lengths. This agrees with a cellular
input that explicitly lists its generators. It is not a bound in bare JSON byte
length for a dimension-only encoding of a huge empty matrix: the producer still
writes vectors of the declared lengths. The input digest records provenance;
algebraic soundness comes from the exact identities checked against the supplied
input, independently of any collision-resistance assumption.
