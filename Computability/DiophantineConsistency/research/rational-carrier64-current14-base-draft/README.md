# Rational-row identity against the current14 syntax provider

Attempt04 checks the complete literal 64/65 graph identity over any
commutative ring under `beta * Urank = MF` and `Wrank = MC - MF`. It also
checks `value65_eq_expressionAt`: for every integer port tuple and every
integer 14-coordinate valuation, the 65-row output equals the integer
evaluation of `CurrentEquationSyntax2011.expressionAt` at those inputs.
The two graph-zero directions are pointwise and use the same valuation.

This client imports the authenticated fresh current14 base syntax object
and Mathlib's ring tactic; it does **not** import the historical Carrier65
object used in the earlier rational specialization. `build_source.py`
derives the identical literal graph rows from the pinned prior generator
output, then replaces the binding theorem with the current14 syntax
binding. The separate read-only `audit.py` verifies 28+5+31 / 28+6+31
JSON row and alias correspondence and the successful receipt. From the
repository root, run:

```
python3 -I -S -B Computability/DiophantineConsistency/research/rational-carrier64-current14-base-draft/audit.py
```

This is an external integer-evaluation binding. It does not yet instantiate
the rational leaves against that integer evaluation, identify the actual
huge fixed ports, or produce an internal iPRA proof for a rational-leaf
expression. The rational-leaf convention does not yield an integer-leaf
64-operation record. The 65-operation printed equation remains unchanged.

Attempt04 passed, Lean exit 0, no warnings or `sorryAx`. The `values_equal`
and `zero_iff` reports list `[propext, Quot.sound]`; the syntax binding
lists `[propext]`. The run used `-M2400`, a 120-second timeout, sampled
3.5 GiB group RSS and 10 GiB available-memory thresholds, nice 19 and idle
I/O. It took 2.446 seconds, peak sampled RSS 1,952,206,848 bytes, with
stable direct guards. Its direct current14 syntax object SHA-256 is
`28e2a026978eb60c2fb0ef494b1c7256a1b1aa354ac4ee9f3688a9433d48daae`;
its captured source SHA-256 is
`112c21a16ddb3d45b311dbe9099ea89619ff6b25f6fb61050d9a7b8f8898d2f9`.
The successful object is
`/tmp/rational-carrier64-current14-base-priority-check04/RationalCarrier64Current.olean`,
SHA-256 `ac3ccf83d8c6c49be8f7b9d306311f2d6fe42f317a4d7fc9b5f875890526b34b`.
The base state/manifest and the direct tactic provider were guarded as
well; inherited transitive and dynamic ancestry and sampled monitoring
remain limitations.

The saved previous attempts explain the development: attempt01 used a
wide evaluator absent from the base, attempt02 left numeral evaluation
unreduced, and attempt03 left numeral casts unreduced and had unused-simp
warnings. Each has its exact source, generator, compiler log and receipt
under `observations/attempt01`–`attempt03`. `overlap-partial.txt` records
the separately interrupted comparison of the historical provider with
the fresh base; it makes no full-closure coherence claim.

| Artifact | SHA-256 |
| --- | --- |
| `RationalCarrier64Current.lean` | `beb7b4e898dddb4f0c8bbf1fcccd24b7d57e56df5b48e53c76754c6d51776ec1` |
| `build_source.py` | `cd3635869afb4f7e1044d873614246077ca77888afdef69777e477a388cbe52c` |
| `audit.py` | `96c10170a7add3a5e95008a84270fc8620aedfdc9a99e50605ed9e1b21fc5b04` |
| `check04.py` | `2a1d59751f35d7bdcaacab8760adabc7d3ef295a0db2b3d304f2d86fcc8b30b0` |
| `observations/attempt04/compile.log` | `5088fa4b24c72b2d1ecf81861e65f33ef0d1b60c92bd0bc194a71fc521b0511d` |
| `observations/attempt04/result.json` | `1aa7f92b832669e21aebae740f5df7ffad372d0ccd76ca7a196d2f58ae0d1ca0` |
