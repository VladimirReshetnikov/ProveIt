# Supplemental batch 213 placement: Sources 180–187

These eight manuscripts arrived in `4b16429bf6d2557b7b168792efa5f487443d6e77`.
Upstream placement `d789bf0a28` already placed them under the formal project's
`proposals/` tree and retired their ZIPs as part of its nine-packet **batch 212**.
Our batch 212 already placed and reconciled the ninth, affine/CM215 packet as
Source 179. This supplemental batch 213 gives the other eight their next host
source numbers and exact recovery references. It is the same delivery, not eight
new arrivals or a second ZIP retirement. Upstream files and historical batch
names remain untouched.

All eight continue the existing `zfc-closure-kernels` report's K215 proof
simplification questions. They are additions, not rival reports; the collection
count remains 290. Written reconciliation and catalogue updates follow this
placement commit separately. No new formal status is assigned by placement.

## Exact accounting

The [map](data/intake213-placement.json) retains all 788 member names, sizes and
raw-byte identities, totalling 10,266,210 expanded bytes across the eight original
ZIPs. Recovery uses **676 immutable Git aliases, 42 earlier delivery aliases,
69 arrival-only members, and one new 21,995-byte ancillary source**. Of the 676
Git routes, 675 bind the upstream placement tree and one binds the exact earlier
`2ca3a5c16f` README. Existing manuscripts/PDFs in the upstream tree are referenced
in place; none is copied again into this host.

The arrival-only routes retain 63 unique log bodies and four checksum-named
records omitted by existing ignore rules, plus two exact original source-byte
variants. Repeated members may point to these originals through delivery
aliases. The five differing expected upstream paths are disclosed in
[the byte-difference record](data/intake213-placement/upstream-byte-differences.json).
They are never substituted for an exact alias. No newline investigation,
normalization, attribute exception, or checksum-manifest content validation was
performed. All original bytes remain recoverable from committed arrivals.

| Manuscript / Source | Arrival ZIP | Existing upstream directory | Members | Git / delivery / arrival / new |
|---|---|---|---:|---|
| 01 / 180 | `K215_Further_Interface_Simplification_2026-10-21.zip` | `further-interface` | 5 | 4 / 0 / 1 / 0 |
| 02 / 181 | `K215_Proof_Contracts_2026-10-21.zip` | `proof-contracts` | 146 | 128 / 0 / 18 / 0 |
| 03 / 182 | `K215_Proof_Simplification_2026-10-21 (1).zip` | `uniform-decoder` | 83 | 68 / 9 / 6 / 0 |
| 04 / 183 | `K215_Proof_Simplification_2026-10-21.zip` | `semantic-coverage` | 172 | 153 / 13 / 6 / 0 |
| 05 / 184 | `K215_Semantic_Proof_Simplification_2026-10-21.zip` | `semantic-proof` | 111 | 81 / 9 / 21 / 0 |
| 06 / 185 | `K215_Shared_Proof_Core_2026-10-21.zip` | `shared-proof-core` | 137 | 120 / 6 / 10 / 1 |
| 07 / 186 | `Sharing_Semantic_Interfaces_Rocq_and_Lean_2026-10-21.zip` | `sharing-interfaces` | 79 | 77 / 0 / 2 / 0 |
| 08 / 187 | `k215-proof-simplification-2026-10-21.zip` | `shared-implication` | 55 | 45 / 5 / 5 / 0 |

The sole new payload is [185-sharedcore-KSim.lean](code/185-sharedcore-KSim.lean),
from archive 06's `semantic_sites/formal/BusyBeaver/ZFC/KSim.lean`, SHA256
`1f4a9c867cc4ff0fb50369c71040e10e775e82902326e6621a57a8528d2ea385`.
The upstream placement omitted it; no exact alias exists in that tree. It is an
inert proposed semantic-contract source, not an edit of maintained `KSim` and
not an adopted proof. It was copied from fresh committed ZIP bytes, never from
a directory where a supplied suite was executed. Delivered relative paths
inside it retain their original context; use recovery to reconstruct that layout.

There are no nested archives in these eight deliveries. Inventory found no
unsafe member paths, duplicate archive names, symlinks, encrypted entries or
compiled proof objects. The recovery helper also enforces member order, type,
source numbering, immutable archive identities and exact final byte totals.

## Review and recovery boundary

All eight have ordinary source dossiers before this placement: archives 01/07
by `review_upstream_reflection`, 02/04/06/08 by `drop_contract`, and the semantic
imports/named-logic scope of 03/05 by `opening_encoder`. Their exact attributed
receipts and [read-credit pins](data/intake213-placement/read-credit-pins.json)
are preserved as metadata. Compiler claims in the deliveries remain submitted
claims. The narrower 03/05 dossier explicitly excludes the machine-specific
site implementations. Each receipt limits its own scope; this placement does
not certify unreviewed implementations. Later selected proof adoption is a
separate checkpoint and cannot be inferred from these reviews.

The own [recovery helper](code/intake213-recover.py) reads Git blobs and ZIP
members only. Run it from a clone with the cited arrival/placement commits:

```sh
python3 SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake213-recover.py --repo . --verify-only
```

It can also reconstruct to a new directory with `--out DIR`; each delivery gets
its own `01`–`08` subdirectory. The actual intake used only streaming verification
and produced [PASS for all 788 members](data/intake213-placement/recovery.json).
The own [negative-control helper](code/intake213-controls.py) rejected a changed
member digest, a missing member, and a valid-but-wrong immutable alias; exact
[results](data/intake213-placement/negative-controls.json) and raw outputs are
retained. No delivered executable, proof compiler, checksum suite, or verification
wrapper ran. The original map stayed unchanged by controls.

[Reader history](data/intake213-placement/reader-history.txt) preserves the first
own mapping assertion and the stopped optional history query. The successor uses
raw archive identities and does not infer a missing mathematical result from a
metadata mismatch. No proof source, producer, old placement, or attribution was
changed. Only the new source, own recovery metadata, this placement note, and a
minimal incoming-queue pointer belong to this supplemental placement.
