# 66/138 integer graph: all-model equivalence and iPRA theorem

The checked Lean source contains the **literal 66-row integer-leaf graph**
from `../current2011-unscaled66/`, at arbitrary integer ports. It proves:

- `evalRing_expressionAt`: its syntax evaluates to the unscaled product
  expression in any commutative ring;
- `scaled_identity`: the maintained Carrier65 value is `Delta` times that
  unscaled value, in any commutative ring;
- `sameZero138`: at the fixed current2011 ports, in every `IΣ₁` model,
  its positively shifted graph and the maintained positive-domain graph
  have the same zero at the **same model valuation**;
- `bridge138` and `standard_equivalence138`: the corresponding all-model
  bridge and a standard-iPRA derivation equating this graph's no-zero
  sentence with intuitionistic negation of the mapped native ZFC-refutation
  predicate.

The proof derives nonzero Delta from the checked positive-beta and positive
shifted-coordinate facts. It has no hypothesis that a zero exists and uses
no division or Pell sign choice. The source rows, 14 witness indices and
four integer-port aliases were compared with the frozen JSON by the separate
read-only `audit_rows.py`. The external graph packet and independent review
check the 66-operation count and exact degree 138; this Lean client does not
claim a formal `totalDegree` theorem, a PDF parsing theorem, or a fresh
source-closure rebuild. The maintained 65/150 page remains unchanged.

Attempt02 passed: Lean and runner exit 0, no warnings or `sorryAx`. The
`evalRing_expressionAt` report is `[propext]`, `scaled_identity` reports
`[propext, Quot.sound]`, and the model/bridge/iPRA reports each list
`[propext, Classical.choice, Quot.sound]`. The run used `-M2800`, 120
seconds, sampled 3.5 GiB process-group RSS and 10 GiB available-memory
stops, nice 19 and idle I/O. It took 3.326 seconds, with peak sampled RSS
2,863,181,824 bytes and minimum available memory 18,853,568,512 bytes.
The guard pinned the coherent historical stage-079 provider and its
recorded direct/companion/shadow inventory; guards were stable. Outer
session 70423 was separately observed to exit 0. Historical transitive,
package and dynamic ancestry and sampled monitoring remain inherited
limits; fresh current14-base objects were not mixed in this search path.

Attempt01 checked the ring evaluation and factor identity but failed
before the model theorem on recursive elaboration of implicit Delta
positivity arguments. Its exact source/generator, log, receipt and outer
exit are preserved under `observations/attempt01/`. Attempt02 supplies
explicit port and valuation types and keeps the large constants locally
irreducible. The successful object is
`/tmp/current2011-unscaled66-model-priority-check02/Current2011Unscaled66.olean`,
SHA-256 `a83b4237c02aa67f24f832f86e58f9afc04510b9ad6768f70f59524c50ad36a3`.

| Artifact | SHA-256 |
| --- | --- |
| `Current2011Unscaled66.lean` | `151dae72af79bf7d4714329ca3bda7a4b3308bb3e3a40d7ae3c14ae16bacd9a3` |
| `build_lean.py` | `5a3747a9e97666633a057551a3f85ce29a5813d8e40b9deae03d7a69a3f2440d` |
| `audit_rows.py` | `937305e1ca597ab8928cdd0d63e40f679bb111e48af1bb041ad566ae2f9fcb02` |
| `row-audit.txt` | `7c2f2ef9ee897d95385430355f1a59e2282c59ab13f3dc377eb65de6f92a8225` |
| `check02.py` | `76814377d072ee000fef99051a6491096309a685169958ce2851d022d1b1713f` |
| `observations/attempt02/compile.log` | `659a55ed5bfc1c07bd9212b68321d6bc577fa6760a3031b9b85b0cdddfbaa4c4` |
| `observations/attempt02/result.json` | `ba49c31dc6daffe99c8ae95fef7e414f63125e435f96bbc574b20218e8e2127a` |
| `observations/attempt02/outer-terminal.json` | `2ed695a02a330c480633ef687e003b47684fbb783890def4db21d7cd92d3077a` |
