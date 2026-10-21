# K215 automatic certificates, concrete credit proofs, and the 214-state search

Research contribution for Vladimir Reshetnikov's ProveIt, 21 October 2026.

Reviewed commit: **`53269bcab1efc0f82d3022645bd7cf0c22d84959`**.
All seven proposal ZIPs then present in `docs/incoming/`, including the newest
`K215_Proof_Simplification_2026-10-21 (2).zip`, are included in the review.
Their hashes and individual contributions are in `evidence/incoming_proposals.json`.

## Main conclusions

- Keep primary K215 as the already certified baseline.
- Adopt the normalized Rocq source proof: 1,426 certificate entries instead of
  2,240, with one computed direction and a proved generic mirror.
- Generate Lean source correspondence from the literal trees and kernel-check
  the materialized cache. The generator is outside the semantic trust boundary.
- Feed the same inferred tuples to the Rocq checker: the additional exact source
  theorem also compiles, so the two proof lanes can share one generator.
- For the shortest additional relative correctness proof, use **CM215**: its
  exact dense/Core transfer is already checked in the incoming proposals.
- For simpler scheduler mathematics, use **ZC215**. This packet proves its exact
  codec, parser, tag-lowering injection, and canonical-prefix credit theorem.
- **No correct 214-state or smaller machine was constructed.** The search
  artifacts report bounded negative results, not a global lower bound.

The full explanation, mathematical proofs, prior-work attribution, numerical
measurements, candidate comparison, and next research directions are in
**`report.pdf`**, with editable source **`report.tex`** and **`measurements.tex`**.

## Contents

| Directory | Deliverable | Boundary |
|---|---|---|
| `rocq_normalized/` | New normalized checker and literal all-register `p215`/`dagPerm` equivalence; application-tested integration patch | Twelve-module Coq 8.18 fresh build and recursive `coqchk`; full Rocq 9.1 binary/ZFC closure remains to integrate |
| `lean_auto/` | Inference algorithm, Lean emitter, generated certificate, kernel acceptance blocks, exact source theorem, offline build driver | Source equivalence; no new binary-machine endpoint |
| `rocq_auto/` | The same newly inferred correspondence accepted by the Rocq checker | Two new modules checked against ten hash-bound dependencies; no second fresh closure or recursive audit |
| `zc_credit/` | Closed concrete parser/codec, lowering injection, both prefix-credit inequalities, protected-head corollary | Canonical scheduler theorem; all-natural literal source-loop bridge remains |
| `search214/` | Twenty-one pinned tables, predecessor-specific elimination and provider search, positive control, independently replayed obstruction | Ordinary simulation argument and finite searches; no successful state reduction |
| `evidence/` | Repository pin, incoming-archive inventory, source/claim audit | Provenance and verification scope |

Each component has its own README, reproduction commands, raw receipts, and
exact source hashes. This archive contains sources and evidence, not toolchain
binaries or compiled proof objects.

## Reproduce the principal checks

Use fresh output directories. The commands do not need a network connection
once the indicated compilers are installed.

```sh
python3 verify_manifest.py

python3 rocq_normalized/build.py --out /tmp/k215-normalized-check --recursive

python3 lean_auto/build.py --lean /path/to/lean-4.32.0-linux/bin/lean \
  --out /tmp/k215-auto-check

python3 zc_credit/verify_concrete_credit.py --out /tmp/zc215-credit-check

sh build_pdf.sh
```

The normalized Coq proof was checked with Coq 8.18.0 / OCaml 4.14.1; its
compatibility aliases are proved from the standard library. Production uses
Rocq 9.1.0, and this packet explicitly leaves that full integration gate open.
The exact Lean toolchain version and printed axioms are recorded in its receipt.
The search README describes the C++17/Python commands and their bounds.

The optional finite ZC parser/source comparison requires the pinned repository
checkout and `ocamlc`; its command is in `zc_credit/README.md`.

## What is new, and what is inherited

The 1,426-entry normalization and shared Lean trees were already delivered in
the incoming normalized Lean proposal. The new Rocq development proves the
corresponding normalization-aware checker and exact source instance. Its mirror
technique comes from an earlier incoming one-sided proof.

The new Lean component derives correspondence directly from the trees; it does
not assume the ordinal pairing is semantically correct. The established checker
validates the result. A staged literal cache makes that validation practical.
The same inferred JSON is accepted by the Rocq checker in `rocq_auto/`, enabling
one generator to serve both proof lanes.

The ZC tag-lowering idea was already in the repository. The new 420-line proof
establishes the concrete codec/parser and all required hypotheses, rather than
postulating a lowering function with the desired properties.

The search is complementary to existing fold and cutpoint searches. Its
distinct coverage is systematic independent rerouting for every deletion target
across the selected 21 tables, with a state-40 provider experiment and independent
positive/obstruction replays. The negative result cannot rule out a smaller
machine using another invariant or representation.

## Most promising next synthesis experiment

The existing high-level simulation already hides spare registers existentially,
but the local increment box specifies their exact physical output. Preserve the
nine logical registers and continuation while permitting any nonempty valid
spare suffix and a legal gap, then resynthesize register excursion, append, and
return together. This admits transformations excluded by exact whole-tape joins.
No candidate implementing that saving is supplied here.

## Integration and attribution

The packet is additive research material. `rocq_normalized/integration/` gives
the concrete source-bridge patch and required production-generator changes.
The Lean README gives its facade integration. The established K215 ZFC endpoint,
CM215 incoming transfers, original compiler/calculus, and machine tables remain
inherited contributions. See `NOTICE.md` and retained component notices/licenses.

The top-level manifest checks file identity only. It does not substitute for
kernel checking, prove a search program sound, or establish consistency.
