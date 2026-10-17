# A complete proof kernel with two shifts and fixed-zero quantifiers

This portable research component uses only two primitive free-name passes:
`up(n) = n + 1` and `down(n) = n - 1`. Its generalization instruction closes
free name zero. Its universal-instantiation axiom opens the displayed binder
at free name zero **without a freshness condition**. All other standard
source-28 logical rules are retained. Theory axioms must be closed.

Arbitrary named quantifier operations follow by uniform shifts. Arbitrary
simultaneous theorem substitutions follow by first generalizing every free
name and only then instantiating the resulting universal closure. Thus no
swap, contraction, or exceptional fused name map is primitive. The two shift
passes have 11 reachable controls each in the retained binary stream codec.
**The resulting count 22 is a sum of stream-transducer control inventories,
not a Turing-machine state count.**

The exact theorem and proof are in `shift22_section.tex`. The mathematical
replacement mechanism is standard, and the repository's source 18 already
describes colliding replacement through GEN/UI/MP. The research contribution
is this fixed-zero shift interface and its tested exact proof transports.

## Reproduce

Python 3.10 or later is sufficient. No third-party packages are required.

```sh
python verify_shift_kernel.py --output shift22_results.json
```

The checked corpus contains all 288 maps on one through four names applied
to actual nested propositional theorems, 30 signed examples, 27 forward proof
cases, 340 reverse proof cases, 122 scanner comparisons, 13 closed axiom
instances, and 31 malformed/prohibited-interface rejections. The JSON also
contains the exact two transducer tables, compact example certificates, and
SHA-256 hashes of the Python sources. Runtime is informational, not stable
across reproductions.

## Files and API

- `shift_kernel.py`: native target checker. Call
  `check_certificate(certificate, theory=())` to reconstruct every line.
  A certificate has an `instructions` list and may assert an exact final
  `conclusion`. Supported name operations are only `up` and `down`.
  `gen_zero` takes a prior `line`; `ui_zero` takes a well-scoped `body`.
  Neither takes a numeric name operand. `ui_zero` permits existing free zero.
- `shift_proof_transport.py`: `translate(certificate, theory=())` converts
  a source-four proof to a target proof and returns `(certificate, audit)`.
  `reverse_translate(certificate, theory=())` converts back to source four.
  `substitute_certificate(certificate, mapping, line=None, theory=())`
  derives an arbitrary simultaneous free-name map of an already proved line
  and returns `(certificate, audit)`. A supplied map covers all its free names.
  An optional `source_kernel` keyword to `translate` accepts the report's
  compatible 24-control kernel. No external module is needed for the default.
- `shift_stream.py`: `encode(formula)`, `decode(bits)`,
  `transduce(mode, bits)`, and `table(mode)`, with modes only `u` and `d`.
- `fixed_search.py`: fixed CP/GIC and EPSC2 axiom emitters and falsity-only
  reference searches. `check_refutation(candidate)` uses CP/GIC;
  `check_epsc2_refutation(candidate)` uses the optional EPSC2 schema.
- `unary_search.py`: prior EPSC1 plus binary-union closed schema and its
  falsity-only reference search. No claim about EPSC1 alone is made.
- `four_kernel.py`, `stream_four.py`: portable source-four reference and
  original codec/scanner implementation used for checking and provenance.
  The target kernel and target scanner reject the removed operations even
  though the reference modules retain them for comparison.
- `verify_shift_kernel.py`: finite, collision-sensitive reproducibility run.
- `shift22_results.json`: recorded result, examples, tables, and source hashes.
- `shift22_section.tex`: polished inclusion section, using ordinary
  `amsmath`/`amsthm` theorem environments, parent `\code` macro, and citations
  `proveit-binder18` and `proveit-source28`.

All compilers operate outside the target checker: they are completeness
witnesses converting proof certificates. The target checker never invokes
their support enumeration, fresh-name choice, or macro construction.

## Four added rows for contraction

For any already proved formula `A`, let `B = close_name(A, 0)`. Derive:

1. `gen_zero(A)`, yielding `All(B)`.
2. `ui_zero` with body obtained by decrementing every free name of `B`.
3. `up` on that axiom, yielding `All(B) -> open_body(B, 1)`.
4. Modus ponens with row 1, yielding exactly `A[0 -> 1]`.

This allows free name 1 already in `A`. The recorded sample is a five-row
certificate: one seed theorem and the four derived rows. The source-19
collision-sensitive UI instance at target zero is a single `ui_zero` axiom.
The generic translation of its ten-row old proof has 76 rows; that compiler
is a completeness witness and does not search for shortest certificates.

## Limits

The two shift maps alone generate only translations. Arbitrary substitution
is derived using quantifiers, so this result does not replace the separate
24-control theorem about implementing all finite maps using name maps alone.
Binding depth, formula recognition, proof enumeration, references, comparison,
axiom generation, and binary-tape compilation still require implementation.
No complete new Turing-machine table or machine state record is supplied here.
