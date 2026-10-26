# Actual current polynomial zero implies syntactic ZFC refutation

Date: 2026-10-26. Author/reviewer of this composition: ROOT. This is an
author receipt; the separate peer reviews identify their precise scope
and prerequisite authorship. All four new sources were read completely
before execution. No assumed native calibration or target-equivalence
premise occurs in the proved endpoints.

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| WangTiles942Soundness.lean (71 lines) | 7380edb40832cc974606eddd2651b9b765712ac9bdb55cdb1ae1e7a83d450068 |
| WangTiles942SoundnessChecks.lean (47 lines) | 4dac8e30913ab909a88c6c648fa20595f016d758866f359232ac3166845e53c8 |
| CurrentSoundness2011.lean (72 lines) | 1118ee3f50dffa046e1205b72a8cac84ef02b5cad0862ef53b79cde1de4ba7ef |
| CurrentSoundness2011Checks.lean (60 lines) | 5af7bd88072198d6ee68022792776aeb8e7104f5faabfc57f17306e41c69319f |

`marked_halts_before_period` takes only an actual `MarkedWord N s a`
and nonzero N. Assuming no blank-run halt before N, it derives an
operating state at every earlier clock. The exact initialization gives
the actual clock1 configuration inside the derived persistent strip.
Iteration of the proved `row_step` yields the actual run encoding at
each clock through N. No live state at clockN is assumed. Coordinate0
stays interior, so its encoded north color is at most433. The full
vertical periodN returns the tile to Start, whose north is435. This
contradiction produces a literal blank-run halt at some t<N.

The stride is any signed integer, N need not be a least period, and the
marker need not be unique. No clean row, no-finish, supplied run,
rectangle or coprimality premise is added. Checks exclude periods1/2
using the actual live configurations at clocks0/1. The [independent
soundness review](wang-tiles942-soundness-peer.md) passed isolated main
and check replay with unchanged inputs and a byte-identical main object.

`CurrentSoundness2011.polynomial_zero_blank_halts` starts with exactly
positive independent coordinates and a zero of the literal maintained
14-variable polynomial. The existing marked-window theorem supplies
its original N, words, carries and actual selected-tile assignment.
Both nonzero modulus instances are derived from N>0. The actual marked
word then supplies the halt above; no word or machine premise is provided
by the caller. `polynomial_zero_zfc_refutation` composes with the existing
`DecimalMachineZFC.blank_halts_iff_zfc_refutation`, retaining the actual
`BProv ZFCax_s [] Form.fBot` conclusion and existing `ConZFC` definition.

Consequently `conZFC_no_positive_zero` proves ConZFC implies no strictly
positive integral zero of the maintained polynomial. At the exact same
fixed K and masks, `conZFC_no_thirteen_positive_zero` transfers this to
all accepted13-variable69/70/71 forms using their already checked
arithmetic equivalences. A focused check also derives a syntactic
refutation directly from a positive zero of any of those three forms,
using the actual restoration map. The maintained evaluator with its
entire actual port tuple is explicitly checked.

Four fresh direct `lake env lean -M6000 -j1` runs passed. Both main logs
are empty; both main objects were freshly saved in the repository object
directory. Checks imported those freshly built mains. All four Soundness
and six CurrentSoundness axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. Check log SHA-256s respectively:
`0020ddae0be0f076e5fad1d9243c6841678696c6ef5a9af1082302ab9de88874`
and `8241505878c44867dbada2ce4b72c600efa4d45ea842441b8326c8fb2df37986`.
The first Soundness development attempt needed `rfl` after an option
case split because Lean had already rewritten the existential target;
the final source passed without warnings or weakened premises.

Existing imported objects were reused. This receipt does not claim a
fresh rebuild of the full arithmetic/machine closure or of incoming
upstream proof simplifications. Their earlier receipts remain scoped to
their recorded source bindings.

The proved implication is **ConZFC → no positive zero**, equivalently
**positive zero → syntactic ZFC refutation**. Its converse, cofinal
canonical tilings, arithmetic/controller completeness, the remaining
frontier equations and an internal-ZFC derivation remain open. This is
not the final requested equivalence. The maintained page still uses the
same complete715-digit decimal integer and14 distinct unsubscripted
unknowns, with unchanged TeX/PDF hashes and equation metrics.
