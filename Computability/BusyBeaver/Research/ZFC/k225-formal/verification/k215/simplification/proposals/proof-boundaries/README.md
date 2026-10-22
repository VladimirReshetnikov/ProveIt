# K215: proof simplification through smaller interfaces

Baseline: `VladimirReshetnikov/ProveIt`, commit
`6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95`.

Start with `report.pdf` or its LaTeX source, `report.tex`. This packet contains
concrete checked components and a proposed larger simplification of the semantic
lower chain. It does not claim a newly rebuilt complete K215 machine endpoint.
The repository was not changed.

## Main results

1. **Local AX annotation erasure.** Infer the 156 successor addresses from the
   literal program instead of repeating them in the certificate. K215's AX source
   changes from 7,563 to 6,533 bytes (13.62% smaller), with no extra imported module.
   The patch also updates the analogous Dom file and their generator. All 35
   modules in the selected client closure were rebuilt from source.
2. **Shared AX alternative.** The two 156-atom words differ only by commuting
   `readp1` past `cons`. Their effects commute by definitional equality on every
   abstract register state. One semantic evaluation now serves both programs.
   The two formal sources change from 322 to 226 lines; including the generator,
   537 to 296 lines. This is an aggregate maintenance saving. The K215-only AX
   import boundary grows by 948 bytes, so choose the local alternative when that
   is the size objective. All 36 modules in the selected client closure passed.
3. **Rocq command/codec interface.** `CommandFactor.v` proves the exact current
   enumerator is fetch/decode/execute/restore, on every natural-valued state.
   Eleven modules compiled and recursive `coqchk` passed under Coq 8.18.0. This
   is an additive, 145-line pilot; shorter client proofs are not yet a net saving.
4. **Direct Infinity.** A serial relation's seed container contains an
   R-successor of each of its members: use the current element itself for the subset variable in the seed
   closure clause. Applying this to tagged raw successors gives ordinary
   Infinity after quotienting. The mathematical core is checked in Lean and Coq;
   the Lean packet additionally connects the argument to the repository's actual
   `FormSeed`, tagged domain and quotient. Final endpoint/interface integration
   remains separate. See `direct-infinity/lean` for the exact checked scope.

**Choose `lean/local.patch` OR `lean/shared.patch`. They are alternatives and
must not be applied successively.** Both contain synchronized producers; each
producer was checked to reproduce the submitted outputs byte for byte.

## Layout

| Path | Contents |
| --- | --- |
| `report.tex`, `metrics.tex`, `infinity-status.tex`, `report.pdf` | Complete report and its compilable source |
| `lean/` | Two AX alternatives, applicable patches, updated generators, audit clients, fresh serial build driver and receipts |
| `rocq-command/` | Exact command-factorization adapter, source provenance and fresh compatibility/kernel-check evidence |
| `direct-infinity/lean/` | Generic core and actual FormSeed/tagged/quotient adapters, replay driver and evidence |
| `direct-infinity/rocq/` | Independent axiom-free generic proof, replay driver and recursive kernel-check evidence |
| `tools/audit_snapshot.py` | Read-only pinned source/import census and literal AX-word comparison |
| `evidence/source-audit.json` | Reproduced 178-module / 2,093,112-byte / 40,517-line endpoint closure and input hashes |
| `evidence/review-summary.json` | Scope of all checks, artifact measurements, and integration boundaries |
| `SHA256SUMS` | File integrity manifest, excluding itself |

No precompiled project object or redundant checkout is packaged.

## Replay

Use a full checkout at the pin above, Python 3.10+ in POSIX/WSL, Lean 4.32.0,
and a complete Coq/Rocq installation. The archived Coq checks used Coq 8.18.0.
The repository's production Rocq lane uses 9.1.0 and is an additional acceptance
gate. The command adapter's driver explicitly records its `Stdlib` to `Coq`
namespace rewrite in temporary copies when run on 8.x.

From the packet root:

```sh
python3 tools/audit_snapshot.py /path/to/ProveIt --output /tmp/k215-audit.json
python3 lean/verify.py --repo /path/to/ProveIt --lean /path/to/lean --variant local
# OR, independently:
python3 lean/verify.py --repo /path/to/ProveIt --lean /path/to/lean --variant shared

python3 rocq-command/check.py --repo /path/to/ProveIt \
  --coqc /path/to/coqc --coqchk /path/to/coqchk --out /tmp/k215-command-check
python3 direct-infinity/rocq/check.py \
  --coqc /path/to/coqc --coqchk /path/to/coqchk --out /tmp/k215-infinity-check
```

For the actual Lean Infinity adapters, use the replay command in that component's
README. The command and Infinity Coq replay output directories must be new.
The Lean drivers serialize proof-tool invocations using the shared project lock;
they rebuild their selected project closure from source.

Check applicability from the repository without applying either patch:

```sh
git apply --check /path/to/packet/lean/local.patch
git apply --check /path/to/packet/lean/shared.patch
```

Compile the report from this directory:

```sh
pdflatex -halt-on-error report.tex
pdflatex -halt-on-error report.tex
```

## Interpretation of the evidence

- The unchanged endpoint source is 54 Lean lines; its large imported development
  and data, rather than that final composition, are the useful simplification
  targets. The source census is independently reproduced here.
- The new AX checks cover both unchanged root-step clients, K215's seeded-program
  theorem, literal-binding checks and assumption profiles. They do not recheck
  the full machine boot/site/source-to-ZFC endpoint.
- Coq command-adapter assumptions are closed. The independent direct-Infinity
  Coq core has eight closed reports and `coqchk -o` reports no axioms.
- Lean's generic seed/tagged-container lemmas need no axioms; its generic quotient
  transport uses `propext`. Actual repository adapters retain the standard
  `propext`, `Classical.choice`, `Quot.sound` profile.
- The direct Infinity theorem supplies an alternative mathematical input. It
  has not yet removed `InductiveAttempts` or the singleton field of `QHyp` from
  the production endpoint. A smaller interface and the complete endpoint gate
  are still required before reporting a net source-closure reduction.
- The existing machine theorem is an external proof-assistant equivalence with
  syntactic ZFC refutability. An internally encoded PA/ZFC derivation remains
  the separate milestone identified by the repository's verification record.

The report credits existing proposals separately from the work in this packet.
The new direct-successor argument is proposed without a claim of literature-wide
priority. Source and contributor attribution is retained in `NOTICE.txt` and
the component documentation.
