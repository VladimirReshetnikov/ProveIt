# Structured literal-ant coefficient prefix

An exact fixed-coefficient construction replacing Report44's dense ternary-Horner prefix. The new prefix has 29,081,374 operations; the unchanged complete-ant main source then yields31,388,831 operations for two raw inputs or31,388,841 for one. Witness domains, all coefficient values, the sole final equation and exact degree 2,304,000 are preserved. This is a construction-specific improvement, with no optimality or novelty-priority claim.

## Contents

- `PROOF.md`: full algebraic compression, geometry ownership and exact ledger
- `full_prefix.py`: new topological1/3-literal arithmetic compiler
- `occurrence_compiler.py`: new event-sweep compilation of fixed instruction-occurrence constants
- `geometry/`: independently authored finite JSON-only colored-union audits, canonical profile API and compact profile evidence
- `data/`: authenticated JSON inputs copied byte-for-byte; these are fixed data, never free arithmetic constants
- `specifications/`: upstream recipe source retained only as `.txt` for inspection, not execution
- `main_source/`: the pinned own-code Report44 arithmetic generator and its three reconstructed JSON component specifications
- `join_strict.py`: literal binding, shifted-ID and domain-preserving adapter for both complete sources
- `SPLICE.md`: exact record transformation and its topology/equivalence proof
- `verification/`: generation and independent audit receipts

The prefix uses only newly authored compiler/profile modules. The joined-source checker additionally reuses the inspected, authenticated own-code Report44 arithmetic generator, hash eafe92d6e57782347f430a4f1d6ea5693bd6a48300d2db0294b3ab7026b96395, with its three reconstructed component specifications. No upstream Python, physical ant/Boolean program, random-access row decoder, fixed coefficient recipe, upstream saved row schedule or upstream saved arithmetic schedule is executed. The new compiler lowers fixed JSON combinatorial descriptions to algebraic gates. It does not simulate an ant or apply the program to a tape. In particular it never reads the `prefix_rows` schedule field.

## Reproduce

Use ordinary, assertion-enabled Python (not `-O` or `-OO`). From this directory, run:

    python full_prefix.py --assets data/recipe_assets --anchor data/anchor_patch.json --out fresh-receipt.json --digest

The expected total is29,081,374 and arithmetic stream hash is6a01d7c1d8ee6b268d49c921b3263b578c152e49c62810d5aa877a4103cb9759. Output is a newly generated compact receipt. Add `--emit new-source.tsv` to materialize every gate; the stream is large and must be written to a previously absent file. Gate records are `id opcode operand operand`; literal leaves are `one` and `three`, and all integer operands refer to earlier gate IDs. `A` includes both addition and subtraction, exactly as in Report44.

The astronomical integer values are never materialized; their finite arithmetic source is generated and checked. The proof, rather than numerical evaluation of those values, establishes equality with the original coefficients. The parent ant, initialization, recoder and endpoint theorems remain inherited dependencies.

To regenerate both complete literal joins, run:

    python join_strict.py --out fresh-joined-receipt.json

This regenerates and binds every old coefficient operand to its actual prefix wire or literal1/3, checks every shifted main reference and declaration, preserves residual metadata and the final equation, and verifies each regenerated own main source against its authenticated canonical hash. The fresh output path must not already exist. No giant integer value is materialized.

## Independent verification

The independent audit checked the exact event identities, every finite geometry profile and correction, all 29,081,374 prefix gates, and all 1,152,598 output labels (the modular numerical check supplements the exact proof). A separate independent adapter then regenerated and validated both complete joined sources with matching hashes. See `verification/independent-prefix-audit/AUDIT.md` and its `JOIN_ADDENDUM.md`; the addendum supersedes the prefix audit's historical pending-join statement. Their checkers retain documented original-workspace paths, while the principal construction and joined reproduction commands above are self-contained.

The compact profile builder additionally reproduced all eleven profile artifacts byte-for-byte in a new output directory. `verification/profiles-relocated-receipt.json` records that check.

Run `python verify_manifest.py` to verify the frozen package byte identities. `MANIFEST.json` excludes itself and incidental Python bytecode caches. No excluded cache is required for reproduction.
