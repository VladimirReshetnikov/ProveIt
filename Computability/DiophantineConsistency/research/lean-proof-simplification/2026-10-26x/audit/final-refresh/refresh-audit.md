# Closing novelty refresh: rounds s-v

Final exclusion-corpus pin: `f42d3f94f78eb63639316a33e25f2f69d12c651e`.
Original source-review pin: `1e2a853935a6155cbcf2aa199aaca51946c4fff9`.

## Result

None of the four retained precise recommendations is repeated by the new rounds s-v. The fresh round v adds six other mechanisms to the exclusion baseline. It does not propose helical reparameterization as a period-one function, a period-one replacement for seam status, the exact CycleBand quotient/binding theorem, multiplication strictness without successor discreteness, or the formula-code constructor-minimum proof.

This refresh concerns novelty. Source equality between the original pin and the final pin, and completed Lean validation, are recorded by the build owner separately.

## Exact corpus identity

Untruncated Git subtree listings were fetched for all four new rounds:

| Round | Subtree Git SHA | Tree entries | Identity |
|---|---|---:|---|
| s | `710b00c537fd3ace3b5dccd0b172a2025636c478` | 66 | Previously audited incoming ZIP: `diophantine-lean-further-simplifications-2026-10-26.zip` |
| t | `173713ce98ade2534d6d5961e51861766263cfaf` | 66 | Previously audited incoming ZIP: `diophantine-lean-further-simplifications-2026-10-26 (1).zip` |
| u | `fe6d16e44d0306ba8fbf30efdc42d657bc3533e3` | 85 | Previously audited incoming ZIP: `diophantine-lean-structural-refinements-2026-10-26.zip` |
| v | `b8d8ffcdf304826603742c71137a14142cfe74dd` | 126 | New `ProveIt_Lean_Simplification_Round3_2026-10-26.zip`, arrival `74c3273be4`, reviewing `22e020937caa81d0cb72a4f63071d6c0bcc1eba9` |

The s-u identity was verified using both their PLACEMENT records and their actual file bytes. Every retained archive file matched the corresponding already extracted incoming ZIP by Git blob SHA-1: 46 files for s, 52 for t, and 60 for u. There were zero mismatches. Only the newly authored placement metadata files, `PLACEMENT.md` and `OMITTED.tsv`, are absent from those extracted originals. See `existing-archive-byte-comparison.json`.

For v, all 38 report, note, Lean, and patch files selected by the audit were freshly fetched and verified against the subtree's Git blob hashes. This includes every report section, the further-questions section, both detailed machine/encoding reviews, the rows README and candidates, validation reviews, the novelty decisions, integration-conflict discussion, and the 45-KB assumed-applied baseline. External Mathlib evidence files and raw provenance ledgers are not new proposal prose and were not needed for this screen. The three s-u PLACEMENT files were likewise retrieved and verified. Four untruncated subtree JSON files and these 41 verified sources give 45 retrieved files, enumerated by `retrieval-manifest.json` with SHA-256 hashes.

## Newly excluded mechanisms from v

The full relative prefix below is `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26v/` at the final pin.

| ID | Newly excluded mechanism | Exact report location |
|---|---|---|
| E1 | Identify the existing none-at-215 state encoding with `Fin.val` after `finSuccEquivLast.symm`; compose injectivity while preserving the sentinel convention | `report/sections/04_encoding_action.tex`, first subsection |
| M1 | Reflect action halt through existing `stateNumber_injective.eq_iff`, `act_stateNumber`, and `stateNumber_none`, retaining target <216 | `report/sections/04_encoding_action.tex`, second subsection |
| M2 | Split the color-after-action proof only at the old head/write location; leave the moved-head conditional symbolic away from the write | `report/sections/05_machine.tex`, first subsection |
| M3 | Use `le_abs'` to convert the exact inclusive absolute-value trace-bound hypothesis into the two exterior cases | `report/sections/05_machine.tex`, second subsection |
| R1 | Guarded integer induction on translated displacement `x-x0` for propagation inside an open interval; remove natural-distance conversions | `report/sections/06_interval.tex` |
| R2 | Derive west and east edge equations simultaneously from one spatially indexed bond signal, making horizontal compatibility substitution | `report/sections/07_pulse.tex` |

The packet also discusses a minor direct `step_head_ne` clarity variant and broad trace-envelope/controller/certificate directions. None is credited as new work in our recommendations. This screen treats all v proposals as available regardless of their uncompiled status or optional framing.

## Comparison against the four retained mechanisms

### Helix/seam period-one rigidity

R1 uses two-sided `Int.induction_on` for a predicate whose propagation premises are guarded by strict interval bounds. It cites the existing `WangTiles942SeamColumns` induction merely as evidence that the induction API is already used in the project. It neither replaces that seam proof nor proves global constancy via `Function.Periodic.int_mul_eq`.

Our exact mechanism derives period one for `s ↦ T (x+w*s) (t-s)` from the helix equation, and separately for the global Prop-valued seam predicate. There is no interval or conditional local propagation. The shared vocabulary of integers and induction does not identify the eliminated obligations. No overlap found.

### Exact CycleBand witness sharing

R2 shares local west/east constructor case analysis through a bond-indexed function. It addresses `WangTiles942StepConstruction`, changes two intermediate edge statement shapes, and preserves its final horizontal matching theorem. It does not expose a quotient word's MarkedWord and band-binding properties before existential packaging. None of the v prose or candidate source proposes the CycleBand/BandMarker factorization. No overlap found.

### Canonical-order strictness and idempotence

No v proposal concerns `ObjectNaturalOrderedSemiring`, the strictness proof from additive differences and no zero divisors, or Boolean idempotence by multiplicative cancellation. The earlier round-c dependency-cycle precedent remains the relevant qualification: generic module reordering is prior work, while the concrete no-discreteness proof is the retained addition. No new overlap found.

### Formula-code constructor minima

No v proposal concerns the lower bound `44 ≤ formCode f`, coordinatewise square-pairing monotonicity, or the numerical outer-constructor minima. Its finite-equivalence and machine-tag arguments preserve different encodings and discharge different proof obligations. No overlap found.

## Review limit

The conclusions are specific to the final pinned corpus. They establish a source-specific non-repetition screen, not mathematical originality throughout Lean or all possible future commits. The main audit and incoming review document the broader earlier exclusions; this note records the closing delta without repeating those reports.
