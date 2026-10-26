# Phase-split native tuple at length2471

The complete ordinary proof in [PROOF.md](PROOF.md) keeps all942 admissible
tiles in the explicit descending weight order, all978 physical positions,
the zero-weight Boolean marker1004, dummy977, and all978 native tests.
It moves the doubled clause from1493 to1462 and uses
`L=2471=7*353`, `d=116137`, `rho=2^47`, `B=rho^L`.
The four complete unsigned fixed ports total **58125 bytes**, versus58829
at the preserved sorted2501 tuple, a reduction of704 bytes. This is a
raw-constant comparison, not yet a rendered-page measurement or a claim
of a global minimum.

The proof is frozen at SHA256
`934c7984038b578a68b1396fffdb8db71a9039b01a86455a74c8639264a1b966`
(932 lines). It includes the full language transport, native recovery,
canonical construction, actual rank and controller, both positive P66
witness maps, and the uniform fourteen-variable Carrier65 corollary.
The separately authored finite certifier binds this exact text and passes
both normal Python and `python3 -O`; all gates use explicit exceptions.
Its default mode compares deterministic bytes without writing.

```
python3 Computability/DiophantineConsistency/research/phase-split-independent/certify.py
python3 -O Computability/DiophantineConsistency/research/phase-split-independent/certify.py
```

Only the explicit `--write` option regenerates the three JSON artifacts.
The frozen certifier SHA256 is
`d7f42234adce10ee050168ebdced4a08b2d2c109910967c17b8b0038b61110ef`;
the deterministic certificate SHA256 is
`f6c576194bfd60d10457c6ba9c43c0b7a8537639588c4f022e7a0362b9051bef`.
The entire doubled3297 array is
`43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93`;
its unscaled array is
`9b33c94814bcbed4a1f0f0e62cdf48d2a026e29c6550470397da7aa491cc0d45`.

| Whole port | Bits | Bytes | SHA256 |
|---|---:|---:|---|
|beta|116137|14518|`4a9d0f18ed31c9f1759c106b71244a8a04caf3c8cf128a7241fc280052825cc4`|
|K|116561|14571|`9a863e00e5f9415c1a07d57959f632d0957eabd6967c58cd7822b1eaa116f449`|
|MC|116137|14518|`c5c1f555895bad3c17c23d3a10e61bb72ff830124be74abca843c01477f88871`|
|MF_source|116138|14518|`aed04479ff9beef8912ffb366b19d3259d672a680d150721c8a0fc2027b8b13e`|

## The changed decoding order

The global cyclic carry bound0..57 is proved before any decoding. A
fractional binary phase `b` gives temporal digits0 or `2^b`, with no
spill because every physical input is Boolean. Separate two ranges:

- For `0<=b<=10`, the complete doubled coefficient suffix is
  `T459=137820284543942`, and `T459+1024+60<rho`. This resets all
  outputs0..1003 before count decoding.
- For `11<=b<=46`, the temporal term at clause1462 is divisible by2048.
  The low clause residue is exactly `2*n+k+x458<=1942<2048`.
  Its mask bits2..10 force it into0..3, so every cell has `n<=1`.
  This preliminary conclusion imposes no label, alignment, occupation
  or marker-value premise. Every low reflected source is a selector
  at position at most526, so its whole contribution is below `2^45`.
  The bound `2^45+rho/2+60<rho` now resets those same fields.

Marker1004 therefore has zero incoming carry in both cases. Its forced
Start unit is odd, its reflected background is even, and the mask requires
an odd temporal digit. This excludes every nonzero fractional phase.
Only then is the full Boolean count lemma used to recover all34 copied
labels. The unchanged uniform Start-cycle proofs exclude whole-field
offsets19 and20; the other offsets force multiple selectors or an absent
source. The real south511 self-loop in the sorted graph is retained.

The previous full-suffix bound `C>=1493` was scoped to an unconditional
`rho/2` temporal bound. This proof changes that method: it uses a
conditional selector bound in the large-phase case. It does not contradict
the preserved [scoped envelope bound](../sorted-selectors-probe/TAIL_ENVELOPE_BOUND.md).

## Complete new recipe and finite interfaces

The sorted `Phi` and all3297 coefficient entries, including zero entries,
are unchanged. Write `Lambda=rho^1462` and retain the fully defined
physical support and copy mask from the proof. The closed recipes are

```
K = rho^18 + rho^1004 + rho^2480 + 2*Lambda*Phi(1/rho)
MC = (B-1) - G951(rho) - rho^960*G26(rho) - rho^1004
MF_source = (B-1) + 8*G917(rho)-4
            + (2^45-4)*Lambda + rho^960*G9(rho)
            + rho^987*G8(rho) + rho^1004
```

Every reciprocal exponent is nonnegative. The unique DC collision is
at1004, with coefficient `1+c'_458=3161095958531`. The clause's extra
Boolean input is selector458; its predecessor1461 has the adjacency sum
plus selector457. The complete product ends at2466; four untested zero
fields2467..2470 give strict representatives. All916 padding fields have
selector-only reflected inputs at most439 and residues0 or2 modulo2048;
their three Boolean units preserve the tested bit3. The origin still
tests bit2. No marker or dummy is inferred from nonzero coefficients.

The full controller uses every prime dividing d:

| Prime | Exact order of2 and B | B | K | B² | 1+BK+B² |
|---:|---:|---:|---:|---:|---:|
|47|23|37|18|6|15|
|7|3|2|0|4|5|
|353|88|21|309|88|224|
|121441|not prescribed|111608|117924|20853|114271|

The fixed-order spacing is6072. The auxiliary prime is
`121441=20*6072+1>d`, and its valuation-one lift is
`B^121440=824827273=1+121441*6792 mod121441²`.
The complete CRT orbit, Boolean subset sums, ordinary safe increments
and both witness directions are proved in PROOF.md, not inferred from
these residues alone.

## Provenance, checks and limits

The exact complete source is the preserved sorted proof
`../sorted-selector-independent/PROOF.md`, SHA256
`d38b5f83ae1b6d342d849e134e1fa341306cb506d68f58fbe74abf9e013cb65d`.
Its finite language still reconstructs all430 actions and all943 old
tiles before deleting exactly the forbidden selector and applying the
full942-element floor-rank permutation. No machine transition is removed.
The accepted decimal page uses the separately checked715-digit seed
decoder; the new native tuple does not change its action sequence.

The ordinary proof is authored by `/root/controller_certificate`, adapting
the complete sorted proof by `/root/complemented47_review`. The finite
certifier is authored by `/root/circuit_reduction`. ROOT and the proof
agent review the new ordinary proof independently; this README does not
claim that the proof author independently reviewed their own proof.
Every accepted predecessor remains unchanged.

The proof author separately read every line of the finite agent's final
certifier, reproduced both modes, and independently reconstructed all430
actions,942 tiles,885481 floor comparisons,3297 coefficients,978 support
positions and four whole ports without importing project code. That
reconstruction also checks all1004 low reflected arrays, both fractional
phase regimes,916 padding arrays, the complete935 offset partition and
two512-state graphs, all fixed prime/order/unit/lift requirements, and
actual rank samples through four cells. The finite packet enumerates
109388 preliminary high-phase count triples,139896 temporal low-residue
cases and218776 full Boolean count quadruples. These finite checks do
not replace the unbounded ordinary argument.

Development checkpoints: marker1003 was considered but its bare18 input
at the marker creates an extra label parity, so this packet keeps1004.
The successful improvement instead splits fractional phases. Length2469
has factor3, where odd d forces `B²=1 mod3`, obstructing this controller;
2471 passes the explicit complete controller requirements. A local
phase10 residue example with512 selectors and temporal1024 shows why
the early count-first argument is restricted to phases11..46. These are
scoped observations, not exclusions of all other encodings or lengths.

The theorem is relative to the explicitly retained ordinary arithmetic,
complete syntactic-refutation and foundational contracts. A checked
finite certificate discharges the new finite premises. No consistency
decision, actual unsolvability, global optimum, or new end-to-end
proof-assistant/internal-ZFC replay is claimed. A complete page, if
materialized, is a separate artifact requiring its own source and visual
review.
