# Independent corrected Grill run-table review

## Final result

The independently derived corrected program has 397,488 run phases, 24,300 positive runs, 373,188 zero runs, 2,030 distinct exponents **including zero**, 2,029 positive exponent values, and maximum exponent 275,944. Its little-endian 32-bit table SHA-256 is `fa658fcdfe1dae2be3a8e2bf97bd613db59558949ea23ca03f549b77201dad01`.

The entire emitted `grill_program.u32` passes exact byte-for-byte comparison with the independent derivation: all 1,589,952 bytes match. Numeric metadata, full exponent histogram, source hash, and program hash also match. No discrepancy was found.

## Independent method

No emitter or upstream program was imported or executed. The reviewer reconstructs the exponent at every phase by decoding its membership in one of three disjoint arithmetic-progression families. This differs from populating selected array positions and leaving defaults. The input is the previously emitted literal Genera table, whose 1,013 IDs, widths, productions, modulus two, and halt ID 1,012 are checked. It uses the corrected theorem pinned to commit `2d887f0fa768fd67f3e545d83f8998b5780e530d`, Git blob `e42c78fabf5c0b0523563e200b52fc1f4b705c53`, fetched read-only and authenticated locally.

For a run phase, split off its source half p and decode its remainder z modulo 7a. Here a=28(1013+1)=28,392 and m=14a=397,488.

- z=17+28y+2r or z=a+13+28y+2r, for r=0,1,2, returns a−3, 7, a−4 respectively
- z=2a+3+14y+2r, for r=0,…,6 and y≠H, returns the seven corrected output values for the actual table's phase-p production
- Every other position is zero

The H output extension is always 3a/2, ignoring the placeholder Genera width and totalized production at H. H retains both sets of L/R-to-E rows and has no E-production rows. Thus a total dummy production at H cannot accidentally compile into a source-halt continuation.

## Exact local checks

The checker streams exact output bytes against expected E/L/R words. SHA-256 is supplementary, not the equality oracle. It never materializes an output generation of more than one million bytes; large paired outputs are compared segment by segment. The largest materialized word is 596,232 bytes.

The selected actual-table rows are 0, 19, 30, 167, 569, 570, 694, and 1011, each at both source phases. They include phase-dependent width-one originals, accepting head, inert symbol, dummy, two pair-alphabet endpoints, and the unique H-producing pair. There are 16 E→LR cases (14 with nonhalting E→LR→E continuation), 36 separate normal L/R→E cases, 54 shifted-erasure cases, and eight complete three-generation cleanup cases. All pass.

The actual H-producing row is pair 694 → [1012,569] at both phases. Its LR cleanup lengths are 880,152; 525,252; and 56,784, giving first emptiness after 1,462,188 further run steps from that LR boundary. Tests also put H in the other position and mix width-one/width-zero neighbors; these are explicitly cleanup-only cases, not assertions that all such source words are reachable.

The whole-table checks confirm that every active position is odd, is below 5a/2 modulo 7a, and becomes a zero run after shifting by 3a. All even phases, all H E-production slots, and the center zero slot of every nonhalting E-production are checked explicitly.

## Mathematical applicability and limits

All nonhalt Genera rows have exactly two outputs at both phases, and widths in {0,1}; the source modulus is exactly two. Therefore the corrected theorem's finite-table hypotheses hold. The Grill program is a nonempty tuple of natural exponents with m≥1, so the native Grill compiler's permitted modulus/program domain has no additional obstruction here. The native lower-slope class count is 2,030, including exponent zero: its one-head slope is 2, still distinct from the zero-head baseline slope 1.

For nonhalt E boundaries, E block length is 7a(2−w), so phase advances by 7aw modulo 14a. Nonhalt L/R block lengths are 7a or 21a, each congruent to 7a; any two-output source generation therefore has a phase-neutral LR return. The single H block has length 10a and introduces exactly the 3a shift used by the cleanup proof.

The literal table's unique H emitter and accepting adapter have been checked structurally: pair 694 is the only nonhalt row producing H; only accepting original 19 produces that pair; all original productions emit only pair/dummy symbols, and dummy reproduces dummy. Combined with the canonical tag semantics and no-short-queue/unique-head proof in `SEMANTIC_CONTRACT.md`, this supplies the halt theorem's unique-first-H and hypothetical-prefix conditions. The checker does not newly prove U15 finite-input universality or canonical-tag reachability.

The exact E numeral/width must still be tied to the arithmetic loader. Arbitrary existential high-zero padding is not justified by this table audit. The native modulus acceptance and the cleanup proof do not pay for full arithmetic composition, source gates, witnesses, or degree bounds. No full arithmetic DAG is materialized or measured here.

## Reproduction

Run `python review_grill_program.py --derive-only` for the independent formula and word checks. Once the emitter's files exist, run `python review_grill_program.py` for the additional byte-for-byte table comparison. Every run is capped at 512 MiB address space and 120 CPU seconds. The exact-byte-word plus table-comparison run used approximately 22 MiB RSS and 18 seconds. Final measured values are retained in `review_grill_program.json`.
