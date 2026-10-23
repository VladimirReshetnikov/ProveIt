# Twenty reusable control proofs for K215

This packet proposes and implements a focused simplification of the correctness
proof for ProveIt's accepted 215-state machine. It is prepared against commit
`cbf94cb552a3b49509e0eee80e7455d4eb5974c6` of
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt).

**Recommendation:** prove the effect of each control suffix once, transport it
across its untouched left prefix with a guarded frame theorem, and finish with a
separately checked read-only return word. Allow the local body to return in state
**1 or 2**. This gives **20 templates / 239 symbolic operations / 1,423 control
occurrences**, improving the earlier `round13-left-frame` proposal's
35 / 444 / 1,422. Two control occurrences remain on the literal proof route.

The mathematical argument, complete template table, current-source baseline,
integration plan, and limitations are in
[`article/k215-framed-control-proofs.pdf`](article/k215-framed-control-proofs.pdf).
The editable source is
[`article/k215-framed-control-proofs.tex`](article/k215-framed-control-proofs.tex).

## What is checked

| Layer | Delivered evidence | Scope |
| --- | --- | --- |
| Independent finite audit | Exact source expansion, all 4,751 decoder routes, all 430 machine actions, affine endpoints, and targeted rejection tests | Executable extraction and binding checks, not a proof-assistant theorem |
| Lean 4.32.0 | Guarded symbolic frame theorem, positive execution, generalized Home return, 20 templates, concrete register engine, source-path framing, and 1,423 caller contracts with actual role-route witnesses | Kernel-checked whole-tape semantics for members of the supplied caller list |
| Coq 8.18.0 | Exact extracted executor definitions, 5 generic closed-assumption reports, 20 closed framed-template reports, recursive `coqchk` with no axioms | Symbolic compatibility component; concrete production tape semantics still needs its client instantiation |
| Current endpoint census | 174 project modules, 1,752,650 source bytes, 37,648 physical lines; external import `Init` only | Static census of current pinned sources, not a fresh complete endpoint build |

The complete Lean control-contract component imports **51 local modules**:
20 unchanged upstream dependencies and 31 new modules, including 23 generated
caller-check batches. This module count is not a replacement endpoint count.
The input table, full tape, unbounded register values, gap parameter, source
instruction, and consumed word are explicit in the contracts.

The accepted dense machine SHA-256 is
`fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.
The accepted native machine SHA-256 is
`9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2`.
Native states 301, 302, and 254 map to formal states 102, 120, and 230.

## What remains to integrate

This packet is additive. It does not replace the production site batches or
rebuild `KEndpoint215`. The principal remaining work is to combine the new
contracts with the existing semantic coverage interface, preserve the two
literal control exceptions and all non-control outcomes, and rerun the actual
endpoint and typed theorem clients. The production Rocq 9.1 adapter is supplied
but has not been compiled in that environment.

The proposed number of expensive local execution obligations is

```text
20 shared control bodies + 2 literal controls
+ 1900 increments + 2850 decrement outcomes + 1 halt = 4773.
```

This is 1,403 fewer than the unshared 6,176 outcome checks (22.72%). All 6,176
source outcomes still need coverage. No end-to-end speedup, net maintained-source
reduction, minimum-template theorem, new internal ZFC derivation, or unconditional
nonhalting result is claimed.

The pinned source already contains computed decoder trees, direct C222
compilation, and a direct full-seed construction. The report credits those
adopted changes instead of proposing or counting them again.

## Reproduce the packet

Python 3.10 or later is sufficient for the integrity, extraction, and generation
checks. Run from this directory:

```sh
python3 verify.py
```

This checks the SHA-256 manifest, independently rediscovers both template
families from the packaged exact source snapshots, and verifies generated Lean
files byte for byte. It uses a fresh work directory and preserves the supplied
evidence. Neither a network connection nor a repository checkout is required.

For a fresh Lean build, supply the **Lean 4.32.0** executable:

```sh
python3 verify.py --lean /absolute/path/to/lean
```

Or build only the Lean component:

```sh
python3 lean/build.py --lean /absolute/path/to/lean \
  --work /tmp/k215-frame-lean-check
```

The build copies the complete import closure to a fresh directory and compiles
sequentially from source. It does not reuse delivered object files. It records
compiler version, commands, imported object hashes, source and object hashes,
raw output, warnings, and reported axiom dependencies. New modules must be free
of warnings and `sorryAx`; their reported axiom dependencies may contain only
the usual `propext`, `Classical.choice`, and `Quot.sound`. The inherited `KZip`
linter warning is recorded separately.

The caller decisions use 23 batches of at most 64 entries. The original
monolithic 1,423-entry decision exceeded an 8 GiB memory limit and is recorded as
a failed development attempt, not accepted proof evidence. Batching preserves
the same statements and composes the checked Boolean results by `List.all_append`.

For the Coq 8.18 compatibility check, copy the component before running its
in-place regeneration/checker:

```sh
cp -R rocq /tmp/k215-frame-coq-check
python3 /tmp/k215-frame-coq-check/check_component.py \
  --coqc /absolute/path/to/coqc --coqchk /absolute/path/to/coqchk
```

Alternatively, the root verifier accepts `--coqc` and `--coqchk` and makes the
fresh copy itself. The Coq sources retain the production-import adapter
`K215LeftFrame.v`; compiling that adapter with Rocq 9.1 and the repository's
`BusyCoq` / `K215F` paths is a separate adoption step.

To rerun the complete current-source census against a checkout:

```sh
python3 audit/endpoint_census.py --repo /path/to/ProveIt \
  --output /tmp/k215-current-endpoint-census.json
```

To regenerate the PDF, use a LaTeX installation with the packages named in the
preamble:

```sh
cp -R article /tmp/k215-frame-article
cd /tmp/k215-frame-article
pdflatex -interaction=nonstopmode -halt-on-error k215-framed-control-proofs.tex
pdflatex -interaction=nonstopmode -halt-on-error k215-framed-control-proofs.tex
```

## Integration entry points

| Source | Public interface / purpose |
| --- | --- |
| `lean/LeftFrame.lean` | `sstep_addLeft_eq`, `runLocal_sound`, `wordEnd_sound`, `runLocal_home_word` |
| `lean/FramedTemplates.lean` | Twenty actual-table local traces and `template_sound` |
| `lean/K215FrameEngine.lean` | Concrete register and Home instances; `template_sound215` |
| `lean/BusyBeaver/ZFC/KPathFrame.lean` | Sufficient-suffix source framing, no-carry guards, natural-subtraction gap rebasing |
| `lean/FrameContracts.lean` | Exact entry/output tape contracts and source/role attachments |
| `lean/FrameCallerCore.lean` | Twenty metadata records and the finite caller checker |
| `lean/FrameCallerBatch000.lean` through `022` | Kernel decisions for all 1,423 delivered records |
| `lean/FrameCallers.lean` | `all_caller_contracts`, `all_caller_standard`, `caller_bindings` |
| `lean/FrameRouteSound.lean` | `all_caller_routes`, producing maintained `RolePath` witnesses |
| `rocq/FrameProofBody.v.inc` | Shared 158-line generic symbolic proof body |
| `rocq/K215FrameTemplates.v` | Same twenty local and universally framed equations |

A suitable additive repository destination is
`Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/framed-control-contracts/`.
The standalone layout deliberately makes review and replay possible before
choosing production module names and changing endpoint dependencies.

## Contents and evidence

- `article/`: report PDF, LaTeX source, and included validation summary.
- `lean/`: complete source closure, portable build script, generators, and exact
  upstream source pins.
- `rocq/`: extracted-definition compatibility component, production adapter,
  exact source snapshots, and successful compiler / recursive-checker evidence.
- `audit/`: independent extraction/discovery and source-census scripts, minimal
  pinned source snapshots, and reproducible finite results.
- `evidence/`: final Lean build records and raw output, current-source census,
  finite replay record, and explicitly marked failed monolithic attempt.
- `MANIFEST.json`: hashes and byte counts of delivered files.
- `licenses/`: retained attribution and inherited notices; see `NOTICE.md`.

Compiler binaries, `.olean` / `.vo` files, downloads, and development caches are
excluded. A source archive is sufficient to reproduce the checks.
