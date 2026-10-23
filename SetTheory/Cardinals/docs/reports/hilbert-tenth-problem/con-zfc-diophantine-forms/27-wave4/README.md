# Smaller Con(ZFC) Diophantine presentations

Reviewed repository pin: `ae3007ca4467011e0e051c84acb4a1dd13971b0e`.
Date: 23 October 2026. Prepared for Vladimir Reshetnikov's ProveIt repository.

Read `report.pdf` (nine pages) or compile `report.tex` twice with pdfLaTeX.
Detailed proofs and exact arithmetic artifacts are included, not just a proposal.

## Recommended constructions

| Criterion | Artifact | Result |
|---|---|---|
| Moderate degree, positive domain | `norms/two_weight_norm12_product.json` | 12 positive unknowns; degree 1081; 120 operations |
| Few integer unknowns, lower cost | `integers/integer24_original_product.json` | 24 unrestricted integers; degree 2432; 163 operations |
| Few integer unknowns, lower degree | `integers/integer24_ratio_product.json` | 24 unrestricted integers; degree 1936; 168 operations |
| Nine positive unknowns, lower degree | `nine/generated/nine_natural-majorant_specialized_positive_dag.json` | 9 positives; degree 120764*5^33+368; 1537 operations |
| Nine positive unknowns, lower cost | `nine/generated/nine_majorant_specialized_positive_dag.json` | 9 positives; degree 161844*5^33+484; 1480 operations |
| Low arithmetic cost for a system | `operations/lift17_Y59.json` | 17 positives; 8 equations; degree 12; 59 operations |
| Integer low-degree lift | `integers/integer51_degree4.json` | 51 integers; one quartic, expressed as 30 quadratic residual squares |

Additional alternatives include 12-positive and 24-integer systems/SOS forms;
the 24-integer degree-2256, 164-operation intermediate;
42-integer sextic and 36-integer octic;
59-operation systems of degree 10, 8, and 6;
and nine-variable versions with independent coefficient leaves before exact
fixed-recipe folding. The top-level theorem always uses the stated domain.
In particular the nine-natural/positive-variable equations must not be read
over unrestricted integers: nonnegativity of the final witness matters.

Compared with our previous delivered packet, 12-positive degree/operations
improve from 1145/123 to 1081/120, and integer low-degree counts improve
from 54/45/39 to 51/42/36. Compared with the wave-3 collection, the moderate-degree
integer count improves from 26 to 24. The unchanged nine-natural-variable
polynomial now has 1485 operations instead of 20531; without using exact
fixed-coefficient recipe equalities it has 1616. The new majorant polynomial
has 1542 operations over naturals, or 1537 over positives.

P67 remains the fewest-operation single equation in the reviewed collection.
The old positive quartic32 and source-23 low-degree 27-integer forms remain
useful. No global minimality, eight-variable theorem, smaller Turing machine,
proof of consistency, or fresh Lean/Rocq endpoint build is claimed.

## One complete fixed coefficient instance

Every new arithmetic packet in this release selects the same whole tuple:
`wang943-mixed-radix4-zero-fields-5pow9`, with B=2^(5^9).
See `INSTANCE.json`, `coefficients/COEFFICIENT_BINDING.json`, and
`coefficients/COEFFICIENT_PROOF.md`.

The four actual integers are `coefficients/expanded/{beta,K,MC,MF_source}.bin`.
They are unsigned, minimal-width little-endian, with no header: 977220 raw
bytes in total. MF_source is already shifted by beta. The `.gz` counterparts
are storage copies, not a claim that the numerical coefficients are small.
The ordered tuple SHA-256 is
`dee7e4646f4b5e78a0200065768a436570b2fae5355d45682450c6a5b80416d5`.
Its definition is concatenation of the four raw files in that order, with
their individual lengths and hashes recorded in the manifest.

The twelve- and integer-variable formulas need only these four fixed ports.
The nine-variable construction additionally uses bounded exact recipes for
its index z,y and factorial-weighted coefficient leaves. Those larger integers
are specified completely but are not expanded. Their aliases and complete
rebinding procedure are in `nine/README.md`; every leaf must be rebound, not
just the four convenient-looking names. No numerical constant is selected
by searching for a halt or a proof of contradiction.

Historical source snapshots and comparisons retain their original tuples.
They document provenance or alternatives; they are not the selected release
instance. The native high mask and shifted source high mask are distinct.

## Reproduce

Python 3.10+ is needed. The finite independent low-degree audit additionally
uses SymPy; this release was replayed with Python 3.12 and SymPy 1.14.0.
Install the declared dependency using your usual Python environment.

Run `python -B verify.py` from any working directory, or pass its absolute path.
It checks sealed hashes and the coefficient/machine binding, then runs fourteen
replay stages in a temporary copy. It compares rebuilt artifacts byte-for-byte
and does not mutate the original archive contents. `--quick` skips replay;
`--out /path/outside/the/release/receipt.json` saves a receipt. Do not use `-O`.
`VERIFICATION.json` is the delivered full replay receipt. To check deliberate
corruptions, run `python -B negative_controls.py`.

Individual directories contain portable generators and checks. The imported
source arithmetic and comparison utilities used by some checks are bundled
and pinned; no network fetch or repository checkout is needed to replay.
The coefficient generator and its independent reconstruction do not execute
the copied upstream coefficient builders.

JSON degrees and exponent fields can exceed IEEE-754 exact integer range.
Use integer-preserving parsing. Gate registers and formal coefficient leaves
are not existential variables; all actual fixed leaves have explicit recipes.

## Evidence and trust boundary

`report.tex` gives the comparative argument. Detailed universal proof notes
cover Galois separation, rational auxiliary-Pell integrality, signed scale,
zero boundaries, negative-scale exclusion, coefficient decoding/carries,
canonical completeness restrictions, and the Jones finalizer.
Independent review and replay files are under `review/` and `root/`.

Finite audits verify arithmetic identities, ledgers, domains in test fixtures,
leading coefficients, literal machine data, finite coefficient geometry,
populations and actual bytes. They do not establish nonhalting or consistency
by experimentation. The claimed ZFC-provable equivalence composes ordinary
mathematical proofs with the pinned native/Pell compiler and K215 calibration;
it is not a newly kernel-checked composite theorem. The nine-variable formal
interface is parameterized `Jones1982.Nine.wset_iff_nine` at nu=32, not the
separate public nu=58 existence route.

## Provenance and incorporation

`COMPARISON_AT_PIN.md` is the reviewed upstream reconciliation. Source ledgers
and copied licenses/notices remain in the corresponding directories.
`SOURCE_ADDITIONS.json` pins the literal machine and formal endpoint copies.
`SHA256SUMS.json` seals this complete release; `VERIFICATION.json` is excluded
from that ledger to avoid a self-referential receipt hash.

The archive is self-contained for the declared finite replays. If repository
placement omits duplicates or checksum files, preserve a recovery map or adapt
the verifier rather than claim the unmodified driver still works in place.

New work was generated with OpenAI assistance for incorporation into ProveIt.
Upstream methods and formalizations retain their attribution and licensing.
The repository's supplied MIT-0 license is retained as `LICENSE.ProveIt`.
