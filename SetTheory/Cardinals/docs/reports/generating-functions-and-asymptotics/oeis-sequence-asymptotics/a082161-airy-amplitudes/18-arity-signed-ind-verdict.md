# Independent verdict: fixed-k compacted and DFA all-finite-orders expansions

Date: 2026-10-02.

**Approved for each fixed integer k≥3 and each fixed finite expansion order.** Both source sequences have the claimed Poincaré expansion with one strictly positive model-dependent amplitude unchanged by truncation order. The proof correctly handles the exceptional DFA seed, completed-run positive comparison, global signed-delay bound, finite-memory tracking, arbitrary formal stages, analytic residuals, and central zero-limit bootstrap.

Reviewed proof `../general-signed-all-orders.md` SHA-256:
`e50fc94256b8dfefd6320991b2f00b12b7b60cce540183b366413bc9d9f10f60`

Detailed audit `analytic-audit.md` SHA-256:
`00f31c6d678d0a9581e4c847271113e82fd2b1ea420b68dc5dd76f711a3c2dd5`

With q=k−1, the first logarithmic normalized-ratio coefficients at n^(−(k−2)) are

- Compacted: (q/k)^k/(k−2)
- DFA: (q/k)^k/[2(k−2)]

All earlier count correction coefficients agree with the relaxed sequence; the coefficient at index 3(k−2) increases by the displayed amount. Both normalized ratios approach their positive limits from above and are eventually strictly decreasing. The first two correction coefficients therefore remain those of the relaxed model for every k≥3.

The independent script, importing no producer code, passes 11,016 checks across all available physical entries for k=3,…,10 and n≤9, including rational transforms, completed-run sums, exact scaled-delay identities, leading ratio conversion, and published table values. The producer's 2,403 checks also replay. The detailed audit provides analytic proofs beyond those finite checks and records all dependency and script hashes.

This approval uses the separately approved relaxed leading and all-orders results. No uniform-in-k theorem, convergent infinite series, explicit amplitude evaluation, all-n monotonicity, or novelty claim is included.
