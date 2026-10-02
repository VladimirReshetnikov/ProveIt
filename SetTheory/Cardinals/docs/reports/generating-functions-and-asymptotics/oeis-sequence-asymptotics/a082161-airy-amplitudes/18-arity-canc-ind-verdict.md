# Independent verdict: logarithmic ratio cancellation

Date: 2026-10-02.

**Approved for every fixed integer k≥3, under the exact source and DFA seed conventions of the already-approved general signed theorem. Safe to include as a proved corollary in the unified report.**

For u_n=C_n/R_n and v_n=B_n/(2^(n−1)R_n), with their strictly positive limits u∞,v∞,

log(u_n/u∞) − 2log(v_n/v∞)
= −(k−1)^(k−1)/k^k n^(−(k−1)) + O_k(n^(−(k−1)−1/3)).

Every preceding fractional power vanishes. The coefficients are −4/27 for k=3 and −27/256 for k=4. The proof's initial conditional status sentence is stale: the exact required signed theorem is approved. No mathematical amendment is necessary.

The audit explicitly verifies nonlinear feedback, the distinction between scalar and endpoint orders, the borderline k=3 case, positive common amplitudes, and the sufficient finite-order analytic remainder. No uniform-in-k claim or convergence of the infinite expansion is made.

## Reviewed SHA-256 hashes

- `../proof.md`: `0990d7d24aa8001e380434f5ba3b20ec487d3bd8a540091820b77add19020dcc`
- `../check_cancellation.py`: `3835d9cc282759486c6f000243d6b370deacd85229e0e65105fbc55894f98365`
- `../relaxed_low_stages.py`: `a2447595c17d5be9314d49d8f204ead8fdcc9d4e9c42a3a212f249a64e9a838f`
- `../check-output.txt`: `7fae4148ef5b9bca700fba969f69053d56a28dfbd55eafdb514c1fea8bbf392f`
- `../../fixed-arity-airy-research/signed-extensions/general-signed-all-orders.md`: `e50fc94256b8dfefd6320991b2f00b12b7b60cce540183b366413bc9d9f10f60`
- `../../fixed-arity-airy-research/all-orders-proof.md`: `7a67a0230c49f4d463fd24c31c94ca04aee32b3a8d1f9382917a6c460804dee0`
- `analytic-audit.md`: `d6e8ecf18d7af6b680521286bfb01de8f1c152af5b4062d7196ac2b1c3bc740a`
- `check_independent.py`: `55ec5a4a9a8bf0dcfd14ba07e535e7b0edd6d38c99c5cf7cd02eae4fca248ed0`
- `independent-output.json`: `533883749460a85163d1c6eb5b872f32c4f33e0afd1473d037a14b8e412f35ea`

The producer's exact symbolic k=3,4 response checks replayed. The independent script imports no producer code and checks original-coordinate delay identities, the scalar conversion, and nonlinear order thresholds for k=3,…,12. The detailed audit contains the argument for every fixed k≥3.
