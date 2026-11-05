# Rational evaluation against current14 syntax

For every four integer ports `p` with `p 0 ≠ 0` and integer 14-coordinate
valuation `v`, Lean proves that the 64-row rational evaluator with fixed
leaves `Urank = (p 3 : ℚ) / (p 0 : ℚ)` and
`Wrank = (p 2 : ℚ) - (p 3 : ℚ)` equals the rational cast of the integer
evaluation of `CurrentEquationSyntax2011.expressionAt p`. The theorem
`rational_zero_iff` gives both zero directions for the same valuation;
`positive_zero_iff` quantifies over all strictly positive integer valuations.
`value65_map` proves that the intermediate 65-row graph commutes with
arbitrary commutative-ring homomorphisms.

The earlier current-base literal graph and syntax-binding check supplies
the predecessor object. This client uses that object plus the fresh current14
base and its Mathlib package. It does not import the historical Carrier65
provider. The fixed rational leaf can be nonintegral, so this is not a
64-operation integer-leaf Diophantine equation. It does not instantiate the
actual fixed ports or establish a new internal iPRA derivation.

The guarded check passed with Lean exit 0, no warnings or `sorryAx`; all
four printed axiom reports list `[propext, Classical.choice, Quot.sound]`.
It took 2.163 seconds with peak sampled group RSS 1,934,413,824 bytes and
stable direct guards. Limits were `-M2400`, 120 seconds, sampled 3.5 GiB
group RSS, 10 GiB available-memory floor, nice 19 and idle I/O. The checked
predecessor object has SHA-256
`ac3ccf83d8c6c49be8f7b9d306311f2d6fe42f317a4d7fc9b5f875890526b34b`;
the direct rational library object has SHA-256
`c1e2ff937444031d0fcb29196353fb43c62c75960ed0e1e00788af13cf8ec579`.
Transitive and dynamic ancestry and sampled monitoring remain limitations.
The output object
`/tmp/rational-carrier64-current14-specialization-priority-check01/RationalCarrier64CurrentSpecialization.olean`
has SHA-256 `d46386e6cec9201c5589eca2328da49144696c32252325160d7329e1b44d2d6e`.

| Artifact | SHA-256 |
| --- | --- |
| `RationalCarrier64CurrentSpecialization.lean` | `54e296167342fbca0f121b985921338d90ae8580e2ce85d30127687768ce279e` |
| `check01.py` | `970ea6463721b6ff432e538fe31d5d9775ccba64594cd9edb99eb1651559a1b1` |
| `observations/attempt01/compile.log` | `adfa741ec6bd582554950952cf3b1c34f46fcb39e5f3b60796f162dac8fd8687` |
| `observations/attempt01/result.json` | `c2145d74a7879cc6644662fe2bb26fe22759570ae92a59ed6dfa037472da661f` |
