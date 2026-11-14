# Closing-decrement variants of PA196

Four new one-row variants retain 196 working states. They do not meet the requested sub-196 target.

From this directory, run `python3 closing_patches.py` to regenerate all four tables, check all 4,959 constrained symbolic instruction contracts, and verify each exact 58,154-step blank startup against the published table. Run `python3 verify_zero_invariant.py` to verify the independent finite zero/nonzero source-invariant certificate.

`closing_variants.md` gives the source-level equivalence argument, evidence boundaries, native/dense row changes, and search results. The input `.lean` files are retained as source references; they are not a standalone Lean build.

The Python symbolic checker assumes the unchanged upstream register-engine macro lemmas. The closing script explicitly checks preservation of their rows. Full source-register equality is checked at every expected primitive endpoint. This is executable mathematical evidence, not a fresh Lean kernel proof.

The three `*_flex_mutants_result.json` receipts cover the same 232,848 tables under progressively refined preconditions; do not add them as distinct candidate counts. Their search implementation is provided in the larger report package. All three found no survivor.
