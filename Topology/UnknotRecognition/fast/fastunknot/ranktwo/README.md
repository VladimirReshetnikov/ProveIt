# Verified rank-two braid compression

Ported from the MIT-0 research bundle `unknot_rank_two_kernels_20261007.zip`,
reviewed from `docs/incoming/` at repository commit `d569a29de`.
The complete source bundle is now preserved as `reports/19/`.
Only the optimizer, dictionaries, shared input utilities, and independent
verifier are included here. The source reference cube is not a production
backend. Existing package licensing applies.

`compress(strands, word, max_passes=1, dictionary='avl')` returns an optimal
one-pass empty/single-letter replacement plan and its certificate.
`verify(strands, word, certificate)` independently replays same-braid equalities.
It verifies soundness, not optimality. `max_passes=None` iterates to saturation
with a weaker total complexity bound. Neither mode finds a globally shortest
braid or decides an arbitrary closed knot without a recognition backend.

The production pipeline uses one AVL pass under a local budget, then replays
before using its output. See `synthesis/ranktwo.tex` for proofs and limits.
