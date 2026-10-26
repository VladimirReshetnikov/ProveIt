> Final novelty classification: PhysicalOrder F is excluded as an exact prior proposal. Its proof-text replay and finite-map tests below are comparison checks only. The selected local families are Sidon S and iterator-depth D; controller O is checked separately. These test counts do not count novel proposals.

# Three-file local candidate checks

Run `python validation/test_local_candidates.py` (also works with `python -O`).
The test script uses only Python's standard library and never invokes Lean.

Sixteen tests pass in both normal and optimized Python. They establish:

- Exact strict-context application of all three patches reproduces candidate bytes.
- An isolated copy of `local_candidates/build_candidates.py` regenerates those candidates, patches, and metrics without changing the author's files.
- Byte-for-byte masking comparison permits changes only to four named proof bodies: `strictMono_fin_eq_self`, `iterate_depth`, `weight_injective`, and `pairWeight_injective`. All text outside those bodies, including definitions, imports, and theorem signatures, is unchanged.
- Source bytes match their pinned Git blob and SHA256 manifest entries; file-level metrics and UNCOMPILED status match.
- No new `sorry`, `admit`, or `axiom` token is added (conservative lexical check, including comments).
- Negative controls catch changed definitions/signatures, added trust tokens, patch source drift, unsafe target paths, and bad hunk counts.

Independent finite models check all 50,070 self-maps of Fin n for n=0 through 6. The only strictly increasing map for each n is the identity (including the empty ordinal). Weak monotonicity, injectivity without order, and a larger codomain are explicitly rejected as substitutes for the theorem's hypotheses.

Sidon tests cover 4,676 pair-sum quadruples (m=0 through 6), 819 diagonal pairs (m=0 through 12), and 7,942 sorted-pair comparisons (m=0 through 9), including 55 sorted swapped-branch cases. Negative examples show why unordered swaps need canonical sorting and why merely injective weights do not imply distinct pair sums.

These are finite mathematical models and static/source checks, not Lean elaboration or proofs of the unbounded Lean theorems. All three candidate files remain UNCOMPILED. These results do not make a novelty determination or endorse a candidate excluded by the prior-proposal screen.
