# Nine-register zero/positive invariant for PA196

The U208 [source optimization dossier](../../docs/pa_consistency_research_2026-10-29/)
uses a joint zero/positive abstraction of all nine registers. We apply the
same kind of abstraction to the imported PA196 source from its clean seed
`commandConfig 25 2 0 0 zeroStore`, whose register vector is
`(2,0,0,0,0,0,0,0,0)`. The first component is therefore the only initially
positive register. The source seed and the trie are bound by SHA-256 to the
files listed in [joint-mask-receipt.json](joint-mask-receipt.json).

A mask is `sum 2^j [register j > 0]`. Increment sets the respective bit.
A zero decrement follows only its zero edge. A positive decrement follows
only its positive edge and allows either zero or positive afterward. Jumps
preserve the mask and halt has no successors. Every concrete successor is
covered by one of these abstract successors, so an invariant containing the
seed and closed under these rules contains every concrete source run from
that seed.

[`verify_joint_mask.py`](verify_joint_mask.py) calculates the least reachable
abstract set, then separately checks its initial inclusion and all closure
obligations. It independently checks the source ordinal graph using both the
path-based and ancestor-interval resolvers. The result contains **274,880**
site/mask pairs, covering **3,810** of the 3,812 sites. Sites 3774 and 3775
are abstractly unreachable. Among reachable decrements, only site 3773 is
forced to read zero, and none is forced to read positive. Site 3773's possible
masks are exactly `{1,5,17,21,257,261,273,277}`.

These eight masks coincide with those reported for site 3847 of the earlier
U208 source in the referenced dossier. The equality is a useful comparison
of the corresponding source regions; it is not a proof that the full
programs, encodings, or machines coincide. The zero-test fact supports the
three-site specialization proved in [ZERO-TRANSFER.md](ZERO-TRANSFER.md),
but the joint abstraction does not identify any *additional* forced-zero
site or unreachable body. It forgets exact positive magnitudes and cannot
exclude transformations justified by relational, three-category, or stronger
invariants. Its finite invariant does not itself generate a smaller tape
table or an internal PA consistency theorem.

Reproduce from the repository root using Python 3.10 or later:

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search/verify_joint_mask.py --output /tmp/pa196-joint-mask.json
```

The output must match the committed receipt exactly. All checks use explicit
exceptions and also execute under `python3 -O`.
