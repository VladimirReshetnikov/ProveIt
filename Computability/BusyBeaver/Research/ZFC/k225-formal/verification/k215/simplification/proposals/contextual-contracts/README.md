# K215: checked components for shorter correctness proofs

Prepared for Vladimir Reshetnikov, 22 October 2026.

**Recommendation:** prove one reusable contract for a local operation and every
admissible surrounding context, then check the finite occurrence bindings.
This packet completes the universal proof part of the existing 35-template
left-frame proposal and the local semantic part of the existing two-node
source-commutation proposal.

The main article is [article/report.pdf](article/report.pdf), with editable
LaTeX at [article/report.tex](article/report.tex). It contains the mathematical
arguments, integration plan, failure cases, provenance, and research questions.

## Review pin and exact scope

- Repository: <https://github.com/VladimirReshetnikov/ProveIt>
- Commit: `cbf94cb552a3b49509e0eee80e7455d4eb5974c6`
- Target: the accepted 215-working-state binary machine, with blank input,
  startup included, two-way infinite tape, and a separate halt.
- No production repository files were modified. This is a proposal and checked
  component packet for incorporation into the repository.

| Component | Fresh result | Boundary |
|---|---|---|
| Lean runtime and source actions | All 35 complete control contracts, including Home, positive whole-tape reachability, and the actual source-action equation | 1,422 occurrence-routing and coverage bindings remain to be formally assembled |
| Rocq runtime | Guarded frame rule and all 35 local replays, lifted to arbitrary symbolic left context | Home and source-action adapters are not ported here |
| Rocq source | Exact two-node commutation equivalence, using pointwise register equality | The source-path / flattened-CFG semantic bridge remains |
| Independent finite audit | Exact tables, decoder roles, source leaves, all template traces, and the 1,422 occurrence assignments | Python evidence, not a proof-assistant coverage theorem |
| Current Lean endpoint inventory | 174 project modules, 1,752,650 source bytes, 37,648 lines, external boundary `Init` | Static current-source census; not a fresh endpoint build |

**Neither full ZFC endpoint was rebuilt.** No unconditional nonhalting or
consistency claim is added. An external Lean/Rocq equivalence and a separately
encoded derivation inside ZFC are distinct proof objects; this packet preserves
that distinction.

## What has been checked

### Lean: complete contracts for 35 control templates

The four new modules are:

- `lean/BusyBeaver/ZFC/KLeftFrame.lean`: guarded append-left naturality,
  finite local replay soundness, a necessary-guard counterexample, and Home
  composition.
- `lean/BusyBeaver/ZFC/KLeftFrame215.lean`: 35 literal template checks against
  the maintained `tm215` table; 444 symbolic steps in total, maximum 39.
- `lean/BusyBeaver/ZFC/KControlFrame.lean`: checked suffix stripping and carry
  conditions imply the exact `RegisterPath.execute` equation for every prefix.
- `lean/BusyBeaver/ZFC/KFramedControl215.lean`: descriptor alignment and the
  combined positive runtime / source-action theorem for all 35 templates.

These four modules total **575 lines / 31,899 bytes** of added reusable proof
infrastructure. This is not a demonstrated net production-source reduction.
The descriptor checks bind entry-state numerals; they do not prove that every
production source occurrence reaches that numeral through its decoder route.

The accepted fresh replay compiled ten project modules (six unchanged
dependencies and four new modules) plus the independently stated closed client
`FrameAudit.lean` with **Lean 4.32.0**. It records 21 axiom profiles, no
`sorryAx`, no new axioms, and no `native_decide`. The complete runtime contract
uses only `propext`, `Classical.choice`, and `Quot.sound`.

New modules and the audit have no warnings. One inherited unused-simp warning
in unchanged `KZip.lean` is recorded separately. The local compiler total of
9.137226 seconds excludes lock waiting and is a component replay measurement,
not a comparison with the production endpoint.

Authoritative evidence: `lean/evidence/receipt.json`,
`lean/evidence/toolchain_boundary.json`, and `lean/evidence/logs/`.

### Rocq: two independently useful components

The checks use **Coq 8.18.0 / OCaml 4.14.1** against byte-identical inherited
sources. Production Rocq 9.1.0 is a separate integration target.

1. **Source:** four sources freshly compiled; recursive
   `coqchk Refactor.TwoNodeCommutation` passed; six selected assumption reports
   are closed. The theorem relates `dagPerm` and `dagPermComm` for every initial
   register file. Only nodes 188 and 190 change. The generic proof transports
   all structured exits, including the loop-restart rules, without functional
   extensionality, a DAG-rank assumption, or a termination assumption.
2. **Runtime core:** nine sources freshly compiled through `LeftFrame.v`;
   recursive `coqchk Refactor.LeftFrame` passed; four selected assumption
   reports are closed.
3. **Runtime templates:** the final `LeftFrame215.v` was freshly compiled
   against those exact nine dependencies; two selected assumption reports are
   closed. No additional recursive sweep of that added client was run. The
   supplied driver can perform a fresh combined ten-source replay and recursive
   check, but the accepted evidence records the actual two-stage run above.

Authoritative evidence: `rocq/source/evidence/result.json`,
`rocq/runtime/evidence/core/result.json`, and
`rocq/runtime/evidence/templates/result.json`, with their raw logs.

Explicit register-box hypotheses in the runtime lemmas are theorem parameters,
not added global axioms. The Rocq local theorem concludes ordinary reachability;
the positive complete Home contract is supplied only in the Lean component.

## Expected reduction and remaining integration

The exact source has 4,751 leaves and 6,176 guarded outcomes. Decrement has two
outcomes. The framed family contains 1,326 continue and 96 break occurrences,
using 35 shared templates. Three control occurrences retain the original
checker: `001/CB1`, `1000111/CC3`, and `11011/CB1`.

The proposed count of expensive local executions is

```text
6,176 - 1,422 + 35 = 4,789
```

That is **1,387 fewer expensive executions (22.4579%)**. All 6,176 occurrence
bindings still need checking. This is an obligation-count projection, not a
measured reduction in endpoint time, memory, source size, or compiled size.

The next implementation steps are concrete:

1. Rebase the repository's semantic-coverage interface and retain its adapter
   from the literal checker. `KSim.Covered` currently requires a successful
   bounded Boolean replay; a semantic `Reach1` proof does not imply that exact
   Boolean evaluation succeeds within its fuel.
2. Prove the 1,422 occurrence bindings: actual source path and action, decoder
   routing, template index, prefix/suffix split, Home scanner premise, and gap
   arithmetic. A descriptor's entry numeral alone is insufficient.
3. Assemble mixed coverage, preserving all remaining literal checks and the
   terminal case. Rebuild the exact endpoint with unchanged literal-table
   hashes, final theorem type, and assumption boundary.
4. For the source simplification, prove the semantic bridge from `p215` to the
   two-node-commuted structured program. Preserve entry, successor order,
   halt-versus-stuck behavior, and control-only or increment-only divergence.
   Retain the current 1,426-entry normalized source certificate until then.

The guarded frame theorem is false at a left-facing empty local list, where
unframed execution manufactures a blank but framing provides a real cell.
The proofs enforce the guard before each local step and deliberately stop at
that boundary. Source suffix operations separately reject stripping or carry
that would escape into the caller prefix. The article explains both guards.

## Archive layout

| Path | Contents |
|---|---|
| `article/` | LaTeX source, compiled PDF, and build instructions |
| `lean/` | Checked Lean modules, exact dependency copies, generators, closed client, replay driver, receipts |
| `rocq/source/` | Pointwise contextual transport and the exact two-node application |
| `rocq/runtime/` | Guarded runtime frame proof and the 35 checked local templates |
| `research/` | Independent audit, source census, and review notes |
| `inputs/` | Pinned finite data and source fragments required by the independent audit |
| `evidence/` | Verification summary, finite-audit result, and current-source inventory |
| `licenses/` | Project terms and inherited notices; component folders retain their notices too |
| `MANIFEST.json` | SHA-256 and size of every delivered file except the manifest itself |
| `verify_bundle.py` | Offline byte-integrity verifier; it does not run proof kernels |

Failed exploratory attempts are explicitly isolated under `history/` or
`evidence/development/`. Their output is not accepted proof evidence. Compiler
binaries, compiled proof objects, package-manager caches, and LaTeX auxiliary
files are excluded.

## Reproduction

Run these commands from the extracted archive root. Python scripts use the
standard library. They do not download dependencies or invoke network services.

### Integrity and finite audit

```sh
python3 verify_bundle.py
python3 research/audit_left_frames.py --inputs inputs --out /tmp/k215-finite-audit.json
```

The integrity check establishes correspondence with the bundled manifest,
not independent authenticity or proof validity. The finite audit is independent
diagnostic evidence. The proof compilers establish the formal claims.

### Lean

Install Lean 4.32.0, then choose a fresh output directory:

```sh
python3 lean/replay.py --lean /absolute/path/to/lean --out /tmp/k215-lean-fresh
```

See `lean/README.md` for exact generator replay and the toolchain boundary.

### Rocq / Coq compatibility components

With Coq 8.18.0 `coqc` and `coqchk` on `PATH`:

```sh
python3 rocq/source/build.py --out /tmp/k215-source-fresh
python3 rocq/runtime/build.py --out /tmp/k215-runtime-fresh
```

Both output directories must initially be absent or empty. The runtime's
inherited `Boot230` contains a large startup reduction, so its full replay is
substantially more expensive than checking the new local template client.
The per-component READMEs describe the optional unpacked-toolchain argument.

### Article

With a standard TeX Live installation providing `latexmk` and the packages
listed in the preamble:

```sh
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

The PDF contains pinned source links; no external image or bibliography file
is needed for compilation.

## Incorporation and attribution

A suitable initial location is a new proposal directory beneath
`Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/`.
Keep this packet's accepted receipts and explicit integration boundaries with
the proposal. It can then be integrated in small source commits, followed by
the full endpoint replays and a measured baseline comparison.

The 35 templates and empty-left decomposition originate in `round13-left-frame`.
The two-node comparison originates in `k215-simplification-3`; whole-node
transport follows the existing `common-macros` proposal. The packet credits
those discoveries and supplies the checked universal completion, pointwise
register transport, concrete applications, and independent audit.

New material is provided under ProveIt's MIT No Attribution terms. Inherited
files retain their original notices and applicable terms. See `licenses/` and
the component `SOURCE_PINS.json` files.
