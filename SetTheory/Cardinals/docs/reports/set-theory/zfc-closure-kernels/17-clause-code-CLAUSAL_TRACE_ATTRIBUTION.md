# Clausal-trace code attribution

`clausal_trace.py` and `check_clausal_trace.py` were prepared for Vladimir
Reshetnikov's research request on 16 October 2026. They provide a new
executable reference implementation of standard signed Skolemization,
ground clausal tableaux, and fair finite-certificate enumeration. No novelty
claim is made for those logical methods.

`qpsc_syntax.py` is copied byte-for-byte from `code/qpsc_syntax.py` in the
incoming `zfc_consistency_proposal.zip` at the audited ProveIt snapshot
`47f3a3602946dfe48803a91a910c646e74637ac8`. Its SHA-256 is
`3c111a05db386143eda47441832c2c83d5c0dab5da8f6adfe1807522457a655e`.
That source was adapted, with attribution, from `code/syntax.py` in the prior
incoming `zfc_tm_pure_subset_research.zip`. The formula construction, its
authorship, and its prior provenance remain attributed to those submissions.
The present work does not relicense third-party code.

The PSC schema's consistency calibration is prior mathematical research.
In particular the accepted equality-free PSC-only calibration, hereditary
saturation and purity cut appear in batch 144 source 08,
`zfc_one_schema_research.zip`, originally arriving at commit
`39409c8c921cccdbd6162c8767c84cfb7df65df1`.

The JSON examples are generic first-order regressions. Neither is claimed
to refute PSC. The PSC search itself only accepts fields `matrices` and
`trace`, regenerates all nonlogical axioms, and has no theorem mode.

From the final package root, reproduce finite checks with:

```
python code/check_clausal_trace.py --output-dir data
python code/clausal_trace.py --prefix 1000
```

The full proof and interpretation of the tests are in
`data/clausal_trace_proof.md`. The implementation is not a formally verified
kernel and has no measured binary Turing-machine state count.
