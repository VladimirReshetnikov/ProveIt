# Qualified baseline census

Repository: `VladimirReshetnikov/ProveIt`, commit
`f25af53c682ea76c57b67c70c976bcaf836b0c91`.

Scope: all `.py` and `.gz` files under
`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Artifacts`, and all `.py` and
`.gz` members of the eight current ZIPs in `docs/incoming`. The archived
reports inside these ZIPs are read as prior art; their presence is not a new
result of this work. No remote or local upstream source was changed.

## Measurement

The repository's existing `Artifacts/validated_arity_refinement/census.py`
was run against the pinned working tree, writing into `research/census`.
It verifies each scanned file against its Git blob identity. Genuine
module/function/class docstrings are removed, the AST is unparsed, and a
final LF is appended. Significant tokens omit encoding, end marker,
newline/NL, indent/dedent and comments. AST nodes include operator/context
nodes. Bytes are UTF-8 after normalization. Runtime: CPython 3.12.14.

The census contains 3,809 source entries, all parseable, with 2,134 distinct
source byte strings and 2,009 entries containing a literal `print('ACCEPT')`
call. Duplicate normalized programs are deduplicated for the small-module
screen. These are inventory figures, not counts of independently correct
checkers. In particular, diagnostic mutants and incomplete prototypes remain
in the repository and are excluded from the qualified records below.

`source_census.json` and `source_census.csv` contain exact paths, all source
and normalized SHA-256 hashes, size coordinates, and archive identities.

## Pooled records, with contracts separated

The coordinate order is significant tokens / AST nodes / normalized bytes.
Each envelope is attained by different programs, unless explicitly noted.

| Contract | Qualified observed envelope | Qualification |
| --- | --- | --- |
| Compact canonical theorem interface | 239 / 255 / 460 | Public grammar and integer/list alphabet are promised, not fully checked. |
| Compact canonical sequent interface, including seeded header examples | 238 / 255 / 455 | Seeded variants move the administrative neutral premise into the header convention. Context assumptions are part of the sequent, not proved theorems. |
| Fully parsed whole-JSON sorted Eq/D interface | 299 / 335 / 580 | Sound on accepted inputs, but completeness is for canonical encodings; some admitted padding aliases have no certificate. |
| Sorted Eq/D interface also allowing restricted expression input | 299 / 335 / 575 | Distinct parser and idealized parser-resource convention. Same padding caveat. |
| Exact canonical public grammar with intrinsic JSON validation | 316 / 358 / 591 | Intrinsic variant admits JSON `true` as an alias for numerical-zero code 1 and permits unused arbitrary JSON prefix records. |

The exact intrinsic checker itself is **316 / 360 / 591**, so the exact
canonical envelope's AST minimum is attained by the older `proper_nodes.py`
program, not by that checker.

All of these measurements are achieved upper bounds on an unknown optimum.
They are not mathematical complexity lower bounds. This distinction is
stated explicitly in the article (`ch01_base.tex`, size-accounting section).

## Attaining source paths

Paths below are relative to `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/`.
For archive entries, the delimiter `!` separates the ZIP from its member.

| Profile | Complete source | Measured triple |
| --- | --- | --- |
| Compact theorem tokens | `Artifacts/checked_presentation/third_delivery/code/token239.py` | 239 / 261 / 549 |
| Compact theorem AST | `Artifacts/checked_reduction/compact/checker_ast255.py` | 245 / 255 / 580 |
| Compact theorem bytes | `Artifacts/neutral_modes/code/checker_bytes460.py` | 266 / 299 / 460 |
| Seeded-sequent tokens | `docs/incoming/ipra_nontraditional_inputs_2026-11-13.zip!ipra_nontraditional_inputs_2026-11-13/sequent_input/checker_tokens239_seeded_sequent.py` | 238 / 262 / 545 |
| Seeded-sequent bytes | Same archive, `sequent_input/checker_seeded_sequent455.py` | 262 / 296 / 455 |
| General-sequent bytes | Same archive, `sequent_input/checker_sequent458.py` | 265 / 297 / 458 |
| Sorted whole-JSON tokens | `docs/incoming/ipra_structural_parameters_2026-11-13.zip!ipra_structural_parameters_2026-11-13/strict/checkers/strict_tokens299.py` | 299 / 343 / 633 |
| Sorted whole-JSON AST | Same archive, `strict/checkers/strict_ast335.py` | 308 / 335 / 667 |
| Sorted whole-JSON bytes | `docs/incoming/ipra_validated_phase_2026-11-13.zip!ipra_validated_phase_2026-11-13/code/checker_bytes580.py` | 309 / 362 / 580 |
| Sorted expression bytes | `docs/incoming/ipra_nontraditional_inputs_2026-11-13.zip!ipra_nontraditional_inputs_2026-11-13/expression_input/code/checker_bytes575.py` | 308 / 358 / 575 |
| Exact canonical tokens and bytes | `docs/incoming/ipra_intrinsic_validation_2026-11-13.zip!ipra_intrinsic_validation/code/checker.py` | 316 / 360 / 591 |
| Exact canonical AST | `docs/incoming/ipra_names_and_scopes_2026-11-13.zip!ipra_names_and_scopes_2026-11-13/exact_bindings/proper_nodes.py` | 329 / 358 / 717 |

## Existing obstructions relevant to proposed improvements

1. The sorted dummy-slot grammar is broader than the grammar on which
   canonical completeness holds. The raw goal `[[5],[1]]` passes the older
   sorted check and ordinarily reads as `S(0)=S(0)`, but the repository proves
   that it has no certificate. The structural shifted spelling is
   `[[7],[1]]`. See `Artifacts/composition_and_dummy_slots/proofs/second_dummy_proof.md`.
2. `Artifacts/equational_transport/experiments/rejected_match_guard/REJECTED_match_guard255.py`
   measures 244 / 255 / 591 but is an explicitly rejected candidate; it must
   not replace the valid AST record.
3. `Artifacts/shifted_shared_leaf/negative/REJECTED_UNSOUND_shared_no_parity.py`
   measures 267 / 298 / 460 but is unsound. Other `negative`, `diagnostics`
   and `experiments` files require the same eligibility review.
4. Exact binding, forbidden-slot masks, intrinsic per-use validation,
   expression readers, sequent headers, structural fresh names, and the
   equation-only Alias/Back naming repair are already present in incoming
   packages. Repackaging one is not a new mathematical reduction.

## Incoming prior art

All eight incoming archives expressly say their requested global complexity
target was not established. Their new contributions are:

- `exact_bindings`: actual-binder codec instead of padding slots.
- `exact_masks`: availability masks fused with scope traversal.
- `intrinsic_validation`: types validated as values are consumed; true as zero alias.
- `names_and_scopes`: equation-only Back/Alias with the one-shape naming repair;
  separate exact-binding checker refinements.
- `nontraditional_inputs`: sequent headers and restricted expression readers.
- `shared_witness_bundles`: variable-source substitution plus endpoint computation
  recovers transport through a two-component common-witness bundle.
- `structural_parameters`: fresh parameters named by finite trees containing their
  local context, goal and packet; separate sorted-checker refinements.
- `validated_phase`: root validation and phase/protocol refinements.

The census is static. It establishes sizes and identifies source contracts;
it does not itself prove the soundness/completeness of every corpus program.
