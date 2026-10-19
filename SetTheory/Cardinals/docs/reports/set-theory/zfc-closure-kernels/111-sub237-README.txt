BEYOND THE 237-STATE CHECKPOINT
Research supplement for ProveIt, 19 October 2026

STATUS
No machine with fewer than 237 working states was constructed. The four
238-state deliveries added in ec480205a1 have the same transition table;
the inherited 237-state candidate already includes their state deletions.
The exact inherited 237-state tables are retained unchanged.

NEW RESULTS
1. A fresh complete mathematical runtime replay of the exact 237-state table:
   8,386 universal guarded cases; 2,261,369 symbolic rules; all 474 rows.
   A new independent all-tape checker proves the final local fold.
2. An independently checked unbounded source invariant: two forced-zero
   decrements and three unreachable instructions. A replacement theorem
   allows two whole unreachable subtrees to be chosen freely. A new runtime
   interface restricts contracts using the invariant and verifies all 8,381
   permitted guards of unchanged237, still using all 474 rows.
3. Explicit, reproducible, scoped searches of helper changes, head and tape
   representations, context-dependent controls, source rotations and
   unreachable-subtree substitutions. None yielded a new binary candidate.
4. A complete 692-bit equational consistency problem, E692, with nine
   operations and eight equations. It combines the inherited E713 and
   structural-witness ideas, optimizes a Boolean formula, and reuses the
   unary binder as selector successor. The full relative model proof is
   included. With the explicitly retained raw-EPSC/ZFC calibration,
     ZFC proves: E692 does not derive N(d,d)=d iff Con(ZFC).
   No TM interpreter or initializer state count is asserted for E692.

START HERE
report.pdf is the 26-page complete report. report.tex, sections/, and
equational/combination704.tex are its editable sources. The report explains
the proofs, exact charges, search boundaries, and remaining obligations.

REPLAY
Requires Python 3.10+ and its standard library. Leave assertions enabled.
Run from the extracted package directory, using a new output directory:

  python3 -B reproduce.py --output-dir /tmp/zfc-research-replay

This checks SHA256SUMS, extracts the original parent in a temporary folder,
reconstructs the inherited tables and startup, checks source/local proofs,
audits the preserved full runtime evidence, independently proves the final
fold, regenerates and independently validates the source product invariant,
and rebuilds every E704/E696/E692 packet against the exact E713 baseline.
It writes commands, logs, comparisons, and replay.json in the chosen output.
It leaves all delivered files unchanged. The retained integrated replay
receipt identifies its exact input manifest, copied to
evidence/replay_input_SHA256SUMS before the receipt was appended. The final
SHA256SUMS additionally covers these two replay records.

For fresh execution of the expensive universal symbolic jobs as well:

  python3 -B reproduce.py --full --output-dir /tmp/zfc-research-replay-full

Full mode reruns the parent's 238-state and 237-state instruction proofs,
the inherited boundary compatibility guard, and the new source-restricted
237-state instruction proof. It compares the complete case-array bytes.

Optional finite discovery replay (requires a C++17 compiler):

  python3 -B research/binary_search/replay_binary_search.py
  python3 -B research/binary_search/replay_binary_search.py --profiles \
    --output /tmp/zfc-binary-profile-replay
  python3 -B research/binary_search/replay_binary_search.py --full \
    --output /tmp/zfc-binary-search-replay

Other search families have their own README and receipts. Negative searches
do not prove minimality. The main correctness replay need not repeat them.

PDF REBUILD
Run twice in this directory, with a normal LaTeX installation:

  pdflatex -interaction=nonstopmode -halt-on-error report.tex

The delivered PDF was rendered and visually inspected on every page; its
final build has no overfull boxes, undefined references, or LaTeX warnings.

FILES
machines/       Exact canonical/inherited237 tables and renumbering map.
vendor/         Original 237-state proof/checker ZIP, preserved byte-for-byte.
verification/   New independent representation/source/runtime checkers.
evidence/       Fresh complete cases, audit notes, reviews, and receipts.
research/       Source invariants and fully scoped finite discovery artifacts.
equational/     Primary E692; E704/E696 checkpoints; builder and full proof.
inputs/         Exact incoming E713 and retained source proof excerpts.
sources/        Retained invariant inputs and restricted-runtime proof section.
licenses/       Original repository/upstream notices preserved from the parent.
PROVENANCE.json Exact inspected commit, archive sizes/hashes and table matches.
SHA256SUMS      Integrity manifest for the delivered files, excluding itself.

ENCODING AND PROOF STATUS
E692.bits contains 692 logical bit characters plus a text newline. Its raw
87-byte E692.bin transport has four trailing zero padding bits, recorded in
E692.bitlength. Padding is not part of the strict logical packet. All
signature, arity, variable-capacity, equation and endpoint fields are charged.

The new results are ordinary mathematical proofs with reproducible finite
checkers and explicit unbounded induction arguments. The existing logical
calibration is retained and cited. This supplement does not add a serialized
Lean/Rocq endpoint for the final machine or an internal ZFC/PA derivation.
The original sub-237 machine target remains open in this work.
