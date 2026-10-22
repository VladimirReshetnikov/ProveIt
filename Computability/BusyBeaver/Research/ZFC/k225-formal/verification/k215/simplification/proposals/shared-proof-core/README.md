# K215: one shared implication core and semantic site contracts

**Checked refactoring proposal, 21 October 2026.**

Baseline: ProveIt commit `2ca3a5c16f0876d2cab842056353c03a1ed2f5f0`.

Start with `article/report.pdf`. The LaTeX source is `article/report.tex`.
The complete mathematical argument, exact scope, integration plan, tradeoffs,
and further research questions are in the article.

## Main result

The latest dominated-implication proof already contains most of the basis
proved by a separate, older `Lukasiewicz.lean` development. Five additional
modus-ponens applications derive S. Taking domination to be `True` gives the
unrestricted interface and removes that duplicate development.

| Measured source or derivation | Before | After |
|---|---:|---:|
| Shared implication MP nodes | 164 | 63 |
| Lean logic source bytes | 42,715 | 18,668 |
| Lean logic source lines | 819 | 426 |
| Rocq implication source bytes | 22,673 | 17,617 |
| Rocq implication source lines | 1,169 | 365 |

The MP comparison excludes the unchanged one-MP `lift_right` rule on both
sides. Counting it gives 165 to 64, with the same 101-application saving.
These are shared schema/source metrics, not minimum-proof bounds, expanded
proof-term measurements, or whole-endpoint build-time comparisons.

The semantic site interface separately adds 124 lines / 5,849 bytes to KSim.
It is infrastructure for removing repeated primitive execution in a later
change; it has not yet removed any of the 6,176 branch obligations. Across
the selected Lean logic files **and** KSim, source falls from 58,861 to
40,663 bytes (18,198 bytes saved). Generation and verification tools are
separate from these proof-source measurements.

## Package map

| Directory | Contents |
|---|---|
| `article/` | Eleven-page article, compiled PDF and LaTeX source |
| `lean_shared/` | Extended generic core, new pure basis adapter, unchanged Tarski bridge tail, synchronized renderer, integration patch, local checks |
| `rocq_core/` | Same abstract proof in Rocq, Nat adapter, unchanged immediate client, source patch, exact renderer, baseline and candidate kernel evidence |
| `semantic_sites/` | Semantic `EdgeContract`/`SemanticCovered` interface, compatibility wrappers, complete 13-module source closure, patch and typed audit |
| `explanatory/` | Checked counterexample showing why zero-step matching cannot replace positive simulation |
| `evidence/` | Snapshot inventory, verification overview, root review and PDF review records |
| `tools/` | Manifest verification and isolated reproduction drivers |

All proof sources are supplied without compiled objects. The source repository
was left unchanged, and no branch or pull request was published.

## Checks actually completed

- **Lean 4.32.0 logic:** fresh 15-module dependency closure and two audit clients.
  The generic core and unrestricted basis have no axioms. Tarski completeness
  and the numerical clients retain their recorded standard axiom dependencies.
- **Lean 4.32.0 simulation:** fresh 13-module closure and one typed audit client.
  Original public calling conventions are preserved. All 15 original `def`
  bodies, including every executable checker definition, are exactly unchanged.
- **Coq 8.18.0:** fresh eight-module candidate closure, eleven closed assumption
  reports, and successful recursive `coqchk`. The baseline was checked separately.
  The inherited namespace spelling `Stdlib` is normalized to `Coq` for this
  available checker; the exact original sources are retained.
- **Generation and packaging:** byte-identical regeneration, preserved public
  headers, exact source hashes, and all three patches accepted together by
  `git apply --check` at the pinned revision.

The packaged reproduction driver was also run in a fresh output tree: both Lean
checks, the Rocq baseline/candidate checks and recursive `coqchk`, source
comparisons, and the progress example all passed. Its record is
`evidence/package_reproduction.json`.

**The full K215 machine endpoint has not been rebuilt for these replacements.**
The production Rocq toolchain is 9.1.0, and its full endpoint remains a separate
integration gate. The phase-nine endpoint checkpoint also predates the latest
58-step focused core build. No combined receipt or new runtime speedup is
claimed here.

The existing external theorem is blank-tape halting iff a finite ZFC refutation
exists. This packet does not provide an internal PA proof or an encoded ZFC
derivation of that equivalence.

## Reproduce the packet

For an integrity-only check, requiring Python 3.10 or newer:

```sh
python3 tools/verify_packet.py
```

For actual focused proof checking, supply a pristine checkout at the pinned
commit, Lean 4.32.0, and Coq 8.18 `coqc`/`coqchk` on PATH:

```sh
python3 tools/reproduce.py \
  --repo /absolute/path/to/ProveIt \
  --lean /absolute/path/to/lean \
  --out /tmp/k215-shared-core-reproduction
```

The output directory must not exist. The driver copies the mutable build inputs
there, verifies source comparisons, and checks the components serially. It
does not edit the checkout or replace the evidence distributed in this archive.
It uses `/tmp/proveit-k215-proof-build.lock`, as the repository's build workflow
does. A passing integrity check is not a kernel check.

The component READMEs give their independent commands. To rebuild the PDF:

```sh
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

## Integration order

1. Review and apply `lean_shared/integration.patch`. It extends the existing
   core, adds `ImplicationalBasis`, replaces the duplicated proof in
   `Lukasiewicz`, and synchronizes the generator. Existing public theorem names
   and the numerical `DomRho8` adapter stay compatible.
2. Review the alternative Rocq route in `rocq_core/README.md`.
   `proof-source-only.patch` adds the generic core and adapter. It deliberately
   does **not** update the live production generator, build order or manifests;
   those changes and the pinned 9.1 endpoint recheck remain necessary.
3. Review and apply `semantic_sites/KSim.semantic.patch` independently. Keep
   the current Boolean site coverage as a producer of semantic contracts.
   A later primitive family can then be replaced by one complete positive
   contract plus exact leaf membership.
4. Rebuild affected transitive descendants and the existing closed endpoint
   clients; refresh source/import and regeneration receipts through the normal
   repository workflow.

The repository also contains a 52-step Nat-only Rocq rendering of about 11,190
bytes. That is smaller than our generic core plus adapter if isolated file size
is the sole objective. This proposal prioritizes shared mathematical structure,
cross-language parity, and reuse of the basis across logical layers.

## Attribution

The machine, calculus, historical proof plans and prior verification are inherited
from ProveIt and its credited sources. `NOTICE.K215.md`, `LICENSE.ProveIt`, and
the component notices preserve their attribution. This packet contributes the
five-MP basis extension and duplicate-proof removal, the paired generic Rocq
implementation, and the semantic site-contract refactor. It makes no general
priority claim for the underlying classical logic identities.
