# Two anchors, a Start-label alignment test, and shorter cells

The complete ordinary argument is in [PROOF.md](PROOF.md). It defines a
new coherent `(beta,K,MC,MF_source)` tuple for the same fifteen-positive-
variable, 66-operation, degree-157 P66 equation. Relative to the retained
ordinary arithmetic and syntactic-refutation contracts, its soundness
is unconditional on the new finite controller condition, and its converse
requires exactly Pc2 in section 11. **Pc2 is now numerically discharged
for this precise tuple** by the separate certificate below. The complete
[independent mathematical review](../../reviews/two-anchor7691-independent-peer.md)
and [root review](../../reviews/two-anchor7691-root.md) pass within the
stated retained contracts. The frozen proof retains its original explicit
conditional formulation for provenance.

The native changes are concrete:

- Keep physical flags at 1095 and 2195 with coefficients `2^44` and
  `2^45`; remove the flag at 3296 and kernel shift 2201.
- Decode both flags with the weighted count `a+2b=3`.
- Use the forced Start's complemented south bit 1 at target 1014 and
  the single copied anchor at target 2195 to recover alignment. Their
  difference 1181 has a unique support representation, while two odd
  temporal tests exclude every fractional phase.
- Use one global carry bound 29 for all local resets. No refined carry
  bound or global carry-free claim is required.
- Move all 872 padding bits into the proved zero band: 18 full fields
  6708..6725 and 26 low bits at 6726.
- Set `rho=2^47`, `L=7691`, `d=361477`. The final field 7690 is allowed
  to be nonzero; its explicit small bound gives `F<q/7`, enough for every
  canonical subset, exact dummy increment and positive-source converse.

There are 981 physical positions, 979 nonzero coefficients, 109 core
tests and 872 padding tests. All 943 genuine tiles, the entire decoder
and seed, and both dummy positions remain. Every fixed coefficient,
mask, copy, clause, phase, reset, origin, canonical rank and P66 witness
map is specified and checked in the full proof.

## Exact finite discharge

ROOT authored [certify.py](certify.py), using the separately reviewed and
hash-pinned full decoder. It constructs the changed coefficients and all
four integers, checks the entire copy/clause/padding support geometry,
and evaluates K through dense reciprocal Horner, direct positive powers,
and whole-integer reduction. It binds the complete source page before
decoding. A receipt from the previous three-anchor tuple is not substituted.

The exact controller results are:

| Modulus | B | K | H = 1 + BK + B² |
| ---: | ---: | ---: | ---: |
| 47 | 42 | 11 | 18 |
| 7691 | 4045 | 5146 | 6993 |
| 2122441 | 1600611 | 926333 | 1324284 |

The fixed orders are 23 and 7690, with spacing
`176870=lcm(23,7690)`. Trial division and all proper-divisor order tests
certify the relevant primes and exact orders, including the full factor
set `{2,5,769}` for 7690. The controller prime is
`lambda=2122441=12*176870+1>d=361477`. Its square and lift data are

    B² mod lambda = 1613482 != 1,
    B^(lambda-1) mod lambda² = 2326944557674
                            = 1 + lambda*1096353,
    0 < 1096353 < lambda.

Together with all three nonzero H residues these discharge Pc2. The
controller prime occurs only in the proof, not the coefficient recipe.

The final verifier SHA256 is
`85cf6b14aab797c3b607b800ebbb3d6e9b51f1be2a3dedf08b8a56fe5da4116c`;
[certificate.json](certificate.json) has SHA256
`7d3db2089a55cefed6afa9e7df8ee5ffcc64d94a628cbffc261abf352dfa5c3e`.
It binds the frozen complete proof
`6df09c6637d32be89b60f767a876f70c1b2be5cf9d047b1add07252a257abe23`.
After reading the entire final verifier, the proof author separately ran
both read-only commands below; both exited zero and reproduced the saved
certificate exactly. ROOT also ran both modes. The independent proof
review is a separate receipt; author reruns are not that review.

```sh
python3 -B Computability/DiophantineConsistency/research/two-anchor-independent/certify.py
python3 -B -O Computability/DiophantineConsistency/research/two-anchor-independent/certify.py
```

All checks use explicit exceptions and survive optimization. Only the
optional `--write` mode regenerates the certificate. The exact integer
ports use minimal unsigned big-endian encoding:

| Port | Bits | Bytes | SHA256 |
| --- | ---: | ---: | --- |
| beta | 361477 | 45185 | `058bbf83145d43a61b8469f1fea58624a0aa288c87d00feb43c1a479d66b11fc` |
| K | 363452 | 45432 | `8011c1e4f45228d35887e3afa5dfa0896b47f059becac9946414cdfc02174a1a` |
| MC | 361477 | 45185 | `b7012768a5fd5667a5d321dac79dd3202054d3f30f9feb32f450f674a493121c` |
| MF_source | 361478 | 45185 | `eb394c3fae964c92dd7e422dcdb55ad0d787a4d04792830743af8b82eca87292` |

Their total is 180987 raw bytes, versus 207214 for the accepted
three-anchor47 tuple. That is a raw-integer comparison, not a printed
character, compression, degree or operation-count comparison.

## Boundary

This research does not claim global minimality, decide consistency,
or supply a new end-to-end proof-assistant derivation. It leaves frozen
predecessors and the maintained page unchanged. Printed-size claims
belong to a separately materialized and reviewed candidate. The
finite discharge proves no unbounded native or Pell lemma; those are
the complete ordinary arguments in PROOF.md and its retained source
contracts. It supplies no new foundational or proof-assistant replay.
