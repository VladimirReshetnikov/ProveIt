K215 PROOF FUSION AND CERTIFIED LOCAL REUSE
=========================================

Research contribution for Vladimir Reshetnikov's ProveIt project.
Prepared October 21, 2026 (Pacific time).

Baseline repository:
  https://github.com/VladimirReshetnikov/ProveIt
Baseline commit:
  6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95

START HERE
----------
Read report.pdf (or report.tex). The principal immediate recommendation is to
interpret the existing dominated-implication theorem in the predicate

  Compilable x := exists p, Contract p x.

This gives a direct compiler from C222/thm222 and removes the intermediate
CDom/thmDom calculus from the active compiler dependency path. The archive
contains checked component implementations in Lean and the Rocq/Coq family.
The machine, state count and final enumerator/seed theorem types are unchanged.

The second component proves exact table-dependency transport for the maintained
Lean symbolic executor, including its Home wrapper. It provides a sound basis
for reusing a baseline execution when a new table agrees on a saved support.
Home readiness, target register semantics, terminal rows and complete source
coverage remain explicit obligations.

STATUS AND SCOPE
----------------
1. Lean compiler: accepted focused fresh build under Lean 4.32.0, with typed
   clients, optional old-API adapter and an original-source comparison.
2. Rocq compiler: accepted focused Coq 8.18.0 build, six closed assumption
   reports and recursive coqchk. Private 8.x copies only rewrite the Stdlib
   namespace to Coq. This is not a production Rocq 9.1.0 endpoint rebuild.
3. Runtime locality: accepted Lean 4.32.0 build of the production dependencies,
   new generic transport library and audit client.
4. Finite replay: all 6,176 guarded outcomes of the 4,751 current K215 sites
   pass an independent Python transcription; footprints are bundled.

The full modified physical-machine-to-ZFC endpoints have NOT been rebuilt.
The per-site support-cover theorems have NOT been instantiated in Lean.
The Python replay is engineering evidence, not a proof-assistant certificate.
No measured full-endpoint speedup, new candidate machine, minimum-state claim,
or unconditional consistency/nonhalting result is asserted.

Static active-closure savings from compiler fusion alone:
  Lean endpoint: 178 -> 177 modules; 65 lines and 2,060 source bytes removed.
  Rocq K215F:     42 ->  41 modules; 59 lines and 1,565 source bytes removed.
Compatibility modules are outside those active closures. Total repository
storage grows slightly. The additional runtime library is not included in
these savings. The main benefit is one fewer derivation layer.

CONTENTS
--------
report.tex / report.pdf    Mathematical account, measurements and integration plan.
lean-fusion/              Lean compiler patch, sources, adapter, typed clients,
                          build driver, accepted check3 logs and static censuses.
rocq-fusion/              Template/generated-source patch, manifest updates,
                          exact focused inputs, adapter, driver and check1 logs.
runtime-dependency/       Exact locality/transport library, audit client,
                          build driver and accepted checked/ receipts and logs.
audit_runtime.py          Independent Python executor and support extractor.
inputs/                  Exact dense table, K230-labelled table and source sites.
evidence/                Replay summary, compressed per-outcome supports, review.
MANIFEST.json            SHA-256 and length inventory, excluding itself.
verify_bundle.py         Standard-library inventory verifier.
Makefile                 Two-pass PDF build.
NOTICE.txt / licenses/   Attribution and inherited terms.

Historical failed elaboration/build attempts are segregated under history/.
They are not accepted proof evidence. A diagnostic sorryAx in one of those
failed logs does not describe the final accepted source or objects.
Compiler objects and downloaded toolchains are intentionally not bundled.
Absolute paths in historical receipts record where the checks actually ran;
use the relative locations above to locate their included sources and logs.

REPRODUCTION
------------
Run these commands from the extracted archive root. Python scripts use only
the Python standard library. Use a fresh output directory for every proof
build. The proof drivers serialize compiler work with the shared Unix lock
/tmp/proveit-k215-proof-build.lock. Lean's standard library is supplied by its
toolchain; all relevant project dependencies are freshly compiled.

Inventory check:
  python3 verify_bundle.py

Finite runtime audit (no proof assistant needed):
  python3 audit_runtime.py --out /tmp/k215-runtime-audit

The replay summary and decompressed footprints should reproduce evidence/.
The GZip payload uses a fixed timestamp. The raw input identities are recorded
in the summary and inventory. The exact dense table is included for identity
and context; this finite replay uses the K230-labelled table.

Lean compiler, with a checkout at the baseline commit and Lean 4.32.0:
  python3 lean-fusion/build_fusion.py \
    --repo /path/to/ProveIt --lean /path/to/lean \
    --out /tmp/k215-fusion-check

Lean runtime locality:
  python3 runtime-dependency/build_runtime_dependency.py \
    --repo /path/to/ProveIt --lean /path/to/lean \
    --out /tmp/k215-dependency-check

Rocq/Coq focused check, using the bundled exact inputs:
  python3 rocq-fusion/check_fusion.py \
    --coqc /path/to/coqc --coqchk /path/to/coqchk \
    --out /tmp/k215-rocq-fusion-check

For an extracted Debian/Ubuntu Coq toolchain, add --coq-root PREFIX where
PREFIX/usr/lib/ocaml contains that installation. The accepted run used Coq
8.18.0 / OCaml 4.14.1. Production acceptance must use the repository's designated
Rocq 9.1.0 / rocq-stdlib 9.0.0 environment. A --repo option can replace the
bundled focused inputs with the pinned checkout plus the supplied overlay.

Independent path-layout census (an estimate, not a replacement proof):
  python3 lean-fusion/path_census.py --repo /path/to/ProveIt \
    --output /tmp/k215-path-census.json

PDF build, with a normal TeX Live installation:
  make pdf
or:
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

The TeX source uses standard mathematical, table, TikZ, listings and hyperlink
packages. No external figures, shell escape, bibliography tool or network
access is required.

INTEGRATION
-----------
Review the report and patches in an isolated checkout at the pin. First check:
  git -C /path/to/ProveIt apply --check /absolute/path/lean-fusion/compiler_fusion.patch
  git -C /path/to/ProveIt apply --check /absolute/path/rocq-fusion/compiler-fusion.patch

Apply only the changes you choose to adopt. The proof drivers do not modify
the checkout. The producer scripts prepare reviewable overlays and patches;
consult their component README files before regeneration. Keep the original
receipts tied to their original source bytes.

For Lean, migrate clients of the old EnumPerm.build to the explicit
EnumPermCompat import, refresh the endpoint's explanatory CDom comment, and
rebuild affected descendants and both closed K215 endpoint clients.
For Rocq, regenerate the maintained templates/copies and rebuild the sparse and
dense endpoint clients on 9.1, refreshing source bindings and assumptions.

For runtime reuse, first kernel-check baseline support-cover theorems. A target
must provide ready equality, target BoxLemmas and terminal-row facts. Reuse
only guards with the same branch, target, fuel, initial state and progress flag;
recheck changed guards and retain the complete source coverage/startup proof.

Then integrate the already proposed normalized Rocq certificate, shorter
implication core and quotient-unification work as separate acceptance steps.
The report attributes that existing work and distinguishes its recorded checks
from the checks performed for this contribution.

EVIDENCE INTERPRETATION
-----------------------
The manifest establishes byte identity relative to this archive, not a digital
signature, theorem, or independent attestation. Receipts record actual compiler
invocations and source/log/object identities. Re-run the supplied proof drivers
with the pinned sources and toolchains to validate the components yourself.
The archive was checked for intact source/log bindings and patch applicability;
the PDF was compiled and visually reviewed. A packaging-only build-lock addition
to the Lean fusion driver does not alter any accepted proof source.
