# Equality orientations and converse-membership source controls

This folder is a self-contained, source-level research experiment for the
ProveIt ZFC consistency-machine project. It provides 64 exactly emitted AX
variants and ordinary mathematical proofs. It does **not** provide a newly
calibrated transition table below 245 states.

## Reproduce

Run with Python 3.10 or newer; no third-party packages or network are needed:

```sh
python converse_theory.py
```

The program checks all pinned input hashes, extracts only the original pure
formula definitions, re-emits the baseline AX, and compares the complete
1,270-operation finest AST sequence to the published AX word. It then emits
and exactly tokenizes all 64 variants. Every variant passes the full symbolic
AX stack contract, retains one destructive `u` read, and preserves the original
GEN/read-cache prefix, ordinary freshness gates, and cleanup. Prefix + eight
row words + tail are checked to concatenate to the recorded source word.

The membership-converse wrapper implementation is also checked in 1,028 small
semantic cases. Those tests check the implementation; the structural theorem
in the report proves the all-formula claim.

## Main result and proof boundary

The 32 variants with `C_G_membership_converse = 0` have the **same numerical
theorems** as the original calculus, by local axiom replacement. Equality
reflexivity and symmetry are derived from the existence/Euclidean anchors
without either membership-congruence row. Both congruence premises can then
be reversed independently. Reversing the Euclidean conclusion uses parameter
exchange and a propositional theorem; reversing equality vacuity preserves
its complete gated schema family. All arbitrary matrix codes remain unchanged.

The extra 32 variants reverse every explicit membership atom in the C/G
wrappers. They have a native full-schema refutation-equivalence proof via
converse relations. Their numerical encodability/calibration and literal
machine composition are separate obligations. The source generator does not
implement a recursive transformation of decoded matrices.

The best exact dictionary count is **493**, versus the previously known
baseline minimum **533**. All variants still have 1,270 finest operations.
The 40 fewer dictionary calls are not a claim of 40 fewer machine states.
Shared grammar cost, entry directions, rank/zero-block restrictions, required
roots and blank initialization must all be included in a state count.

## Files

- `converse_encodings.tex`: full proof of the equality family, converse-membership
  theorem, scope of the numerical bridge, and source metrics.
- `formalism_inventory.tex`: ZF/ZFC/Foundation calibration, CP/GIC/IR and the
  relative-falsity encoding, an explicit equality-free SIR proof translation,
  subset-only positive closure, and finite class/algebraic comparison.
- `converse_theory.py`: deterministic source generator and exact dictionary DP.
- `converse_source.json`: every source variant, operation count, minimum word,
  AST, exact row decomposition, root override and hash provenance.
- `reference/`: unchanged pinned pure-definition sources, input data, licenses,
  upstream notices and identity manifests.

Both `.tex` files are report sections requiring `amsmath`, `amssymb`, `amsthm`
and `theorem`/`lemma` environments. They can be included in the main PDF.

## Variant keys and compiler input

Use `converse_source.json["anchored_variants"]` for the complete family.
The six bits in a key are:

| Field | Meaning |
|---|---|
| `anchor` | Coupled direction of the existence atom and both Euclidean premises |
| `r3` | Reverse the sole equality premise in rho3 relative to that direction |
| `r5` | Reverse the sole equality premise in rho5 relative to that direction |
| `r7c` | Reverse the Euclidean conclusion relative to that direction |
| `ev` | Absolute orientation of the equality-vacuity endpoints |
| `mu` | Reverse explicit C/G membership atoms |

The minimum-call member is `anchor0_r31_r51_r7c1_ev1_mu0`. The exact original
is `anchor0_r30_r50_r7c0_ev0_mu0`. Each member supplies
`root_word_overrides = {"76": minimum_AX_word}` and `raw_AX_prefix`,
`raw_AX_rows`, `raw_AX_row_numbers`, and `raw_AX_tail`. Its minimum and raw
spellings have identical finest operation sequences. A compiler may use a
different dictionary segmentation or row order when separately verified.

The four simpler controls remain under `variants` as `original`,
`converse_membership`, `converse_equality`, and `both_converses`. Top-level
`modified_AX_word` retains the initial membership-only control for compatibility;
it is **not** the minimum-call variant. Grammar search results belong to the
main packet and may prefer a word with a larger dictionary count.

## Attribution

The original SIR theory and source machine are Mira-Cult's, with Jeff
Ketchersid's end-to-end Rocq verification and Wade's compiler framework.
The pinned emitter and proof infrastructure come from ProveIt and the prior
`zfc245-proof-20261018` and `zfc-axiom-symmetry-20261018` packets. Imported files
are unchanged and retain their manifests and notices. The new work is the
explicit orientation family, direct local replacement proof, source generator,
measurements and accompanying comparison, without a claim of exhaustive
historical novelty or a new Busy Beaver bound.
