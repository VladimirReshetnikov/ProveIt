# Independent composition review

Reviewed2026-10-21. Inputs: owned check_combined.py and BalancedNormalized.proposal.v, compared with inert upstream BalancedBisim.v, NormalizedBisim.v, PathCodec.v, Bisim230.v and RM.v. Only the owned Python checker was executed. No received code or Rocq proposal was compiled.

Verdict: no semantic error found in the normalized-plus-balanced composition. Owned replay passes1426entries,2851branch obligations,32961balanced lookup-node visits versus2033059linear-cons visits, maximum12lookup visits.2659individual endpoint comparisons fail literal equality, demonstrating why normalized ibeq cannot be replaced by ordinary exact equality.

Specific checks:

- Path bit order: JSON sentinel encoding strips the leading binary1 and reads the remaining path MSB-first. Rocq positive PathCodec recursively exposes low bits first. The checker correctly reverses binary digits for the packed Rocq literals and asserts equality with every JSON entry. Empty path1 and internal/trailing zero bits survive.
- Source binding: trees.json is independently reconstructed from literal t215/tD declarations, including node order and primitive arguments. Current-main literal declarations were separately shown unchanged in round10_review/TREE_BINDING.json. The replay is finite evidence over those trees, not a new kernel proof that Lean and Rocq program literals coincide.
- Pointer arithmetic: walk pads beyond finite paths with0; inc wraps at fixed length; brk strips rightmost zeros then increments; cont strips rightmost ones. These match RM.v. The terminal segment returns original incoming P, not the consumed leaf prefix, exactly as Bisim230.seg does.
- Fuel: Python1000iterations includes the terminal halt/decrement inspection, matching seg_fuel1000 and the Rocq S-fuel case. No off-by-one relaxation found. Recursive tree walking needs no extra fuel because the explicit finite trees contain no TX nodes.
- Increment counts: Counter equality preserves multiplicities and ignores increment order, the intended cnt_eq semantics. This is appropriate for commuting natural-register increments between tests, not arbitrary operations.
- Normalization: rstrip('0') equality is exactly equality under trailing false padding for finite Boolean lists. Both paths use this test. The proposal preserves cnt_eq and ibeq verbatim from nbranch_ok.
- Lookup: each internal cut is checked against its left subtree size; flatten equals0..1425. Every in-range lookup is compared with the original entry and1426rejects. The generic Rocq lookup_flatten/getTree_flatten theorem handles all natural indices under valid, beyond the concrete finite test.
- Types: PathCodec.plain_entry and Bisim230.entry unfold to the same product(list bool * list bool * N * N), so no semantic conversion is needed. Imported BalancedBisim and NormalizedBisim share Bisim230 rather than separate incompatible entry types.
- Glue: nbbranch_flatten uses getTree_flatten; nbentry preserves halt and same-register decrement cases; nbcheck preserves initial empty-path branch and all entries; ncheck_one_sided_iff supplies the all-register result after flattening. No reverse certificate or new consistency premise is introduced.

Remaining obligations are correctly disclosed: instantiate a literal CTree over Normalized215, prove validb and nbcheck for actual ptree terms, compile the glue and concrete facade, and rebuild affected endpoint consumers. The finite replay does not discharge these obligations. Lookup-node counts exclude construction, checking validity, segment execution, and proof elaboration; they are not whole-build speed claims.
