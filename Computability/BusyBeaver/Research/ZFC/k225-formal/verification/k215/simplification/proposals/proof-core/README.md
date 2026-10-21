# K215: smaller implication proofs and a checked four-scheme calculus

Research contribution for ProveIt,21 October 2026.
Baseline commit: `aa66d0a33f1f8237a348899eb8095b045a502832`.

Start with **report.pdf**; **report.tex** and its three small `.tex` inputs
are the complete editable paper. The paper distinguishes new results from
the three research packets already present at the baseline commit.

## Results

1.  **A smaller compatible implication proof.** The maintained `DomRho8`
   proof is factored through an arbitrary carrier and implication operation.
   The generic theorem needs only MP, restricted rho8, and a reflexive
   relation preserved by insertion in either implication operand. It needs
   no truth axiom, least element, arithmetic, decoder, injectivity, special
   zero identity, or separate transitivity assumption. Thirteen checked MP
   shortcuts reduce 117 numbered helpers to 84; 82 suffice for unrestricted
   rho8. A direct composition/exchange/K/Peirce argument removes the local
   deduction calculus. Including the new dependency, source drops from
   30,114 bytes / 517 lines to 22,278 bytes / 458 lines (26.0% fewer bytes).
2.  **Four explicit schemes suffice.** In rho(a,b,c,u), allow only the four
   first-argument shapes `u`, `x→u`, `(u→x)→y`, and `((x→u)→y)→z`.
   These schemes plus MP derive every unrestricted rho instance. The
   abstract theorem is checked in Lean and Rocq. A separate Lean adapter
   proves `CFour n ↔ C222 n` for every raw numerical code, and the
   corresponding consistency equivalence. All other C222 rules, including
   truth and the two bundle guards, are retained. This does not compile a
   new source enumerator or machine.
3.  **An exact normalized/balanced certificate refinement.** The new Rocq
   wrapper combines the previously supplied 1426-entry normalized source
   certificate with previously supplied balanced lookup. It proves the
   original all-register source equivalence by equality of checkers. It
   reduces counted lookup visits, but its recorded concrete module build
   was slower than the normalized-list baseline; no runtime speedup is
   claimed.
4.  **An optional shared halting bridge.** The new KSim adapter reuses the
   existing PositiveSimulation theorem. KSim itself shrinks by 31 lines,
   while first-use total source grows by 131 lines. Public types and axiom
   reports are unchanged. This is useful through reuse, not standalone
   source compression.
5.  **State-reduction research and a logical obstruction.** The search
   explores edge-specific state elimination across seven 215-state tables,
   then examines FT215 engine shortcuts and protected decoder reallocation.
   It produces no verified 214-state machine and no global state lower
   bound. A separate Lean hidden-coordinate model blocks one logical-only
   vacuity recovery strategy; it does not model the full ZFC seed bundle.

For the shortest route to another complete 215-state endpoint, the report
recommends **CM215** relative to the already verified primary machine.
Its existing exact-machine transfer minimizes new mathematics, but its
final full-ZFC adapter closure still needs the documented integration
check. M124/FM215 is attractive for small local marker invariants;
zero-credit variants have a cleaner independent scheduler.

## Contents

| Directory/file | Role |
| --- | --- |
| `report.tex`, `report.pdf` | Complete research paper and compiled version |
| `proofs/` | Pinned minimal Lean dependencies, generic and four-scheme Lean/Rocq proofs, numerical clients, patches, fresh-build drivers and receipts |
| `generation/` | Original implication source, thirteen substitutions, deterministic source generators, finite discovery search and provenance |
| `source_checker/` | Normalized/balanced refinement, concrete certificate, minimal Coq dependencies, source bindings, replay driver and recursive-check logs |
| `machine_research/` | Exact machine inputs, bounded searches, FT shortcuts/allocation follow-up, finite certificates and hidden-coordinate proof |
| `provenance/` | Incoming-archive hashes and inherited notices |
| `MANIFEST.json`, `verify.py` | Archive integrity and source-to-receipt binding audit |
| `LICENSE`, `NOTICE.md` | Repository license and inherited attribution |

## Lightweight audit

From the archive root, with Python 3:

```sh
python3 verify.py
```

This checks delivered hashes, exact binding of compiler receipts to
sources, numerical source bindings, claimed size counts, and the lookup
operation counts. It does **not** invoke a proof assistant or prove a
machine correct. Formal replay and search replay are explicit commands.

The proof-generation bundle also supports independent checks:

```sh
python3 generation/generation/regenerate.py --check
python3 generation/generation/specialize_four.py --check
python3 generation/generation/search_shortcuts.py
```

The first two reproduce exactly the delivered proof sources. The third
replays the finite 2,944-option schematic discovery search; it is not a
minimal-proof search.

## Formal replay

Use Lean 4.32.0 and Coq 8.18.0, with fresh output directories:

```sh
python3 proofs/run_checks.py --lean /path/to/lean \
  --build-dir /tmp/k215-proof-core
python3 proofs/run_checks.py --lean /path/to/lean \
  --build-dir /tmp/k215-four-calculus \
  --roots BusyBeaver.ZFC.KCodeFourShape
python3 proofs/run_rocq_checks.py --coqc /path/to/coqc \
  --coqchk /path/to/coqchk --build-dir /tmp/k215-rocq-core
python3 proofs/run_rocq_checks.py --coqc /path/to/coqc \
  --coqchk /path/to/coqchk --build-dir /tmp/k215-rocq-four \
  --module FourShapeImplication
python3 source_checker/reproduce.py \
  --out /tmp/k215-source-refinement --recursive --baseline
```

The source checker resolves `coqc` and `coqchk` from PATH. The Lean and
Rocq proof drivers take explicit tool paths. See `proofs/README.md` for
exact declarations, theorem scopes and translator commands. Machine
research has its own portable replay scripts and tool requirements.

Recorded successful proof runs:

- 28-module fresh Lean closure for the compatible proof, unchanged
 KCodeDom client, optional KSim adapter and subterm example;
- 13-module fresh Lean closure for the four-scheme numerical client;
- 30 distinct project Lean modules across those two closures;
- fresh compilation and recursive `coqchk` for each of the two abstract
 Rocq cores;
- fresh 15-module Coq source-certificate check plus recursive `coqchk`;
- a separate Lean check of the hidden-coordinate logical model.

Generic and four-scheme results and the CFour equivalences have empty
Lean axiom reports. Both abstract Rocq cores' public theorems are closed
under the global context. The existing numerical compatibility interface
retains its old `propext`/`Quot.sound` dependencies.

**The full production K215 machine-to-ZFC endpoint was not rebuilt.**
The main Lean replacement was checked against unchanged downstream
calculus source. The Rocq core is standalone and still needs its numerical
production instance. These boundaries matter when incorporating patches.

## Suggested integration

1. Add `DominatedImplication.lean` and replace `DomRho8.lean` with its
  compatible adapter. The complete patch is in `generation/patches/`;
  `proofs/DomRho8.patch` is the adapter-only diff, so also copy the core.
2. Update the upstream proof generator and run the full production
  endpoint closure. The delivered generator can reproduce this proof
  byte for byte without storing a proof-search transcript in the trusted
  code.
3. Keep `FourShapeImplication` and `KCodeFourShape` as a separately checked
  research formalism until an enumerator and physical table are built.
4. Port the generic numerical instance into the maintained Rocq lane,
  then run that lane's full endpoint and assumption checks.
5. Adopt normalized certificates according to existing incoming work;
  benchmark before switching to balanced storage.
6. Apply the optional KSim abstraction where cross-machine reuse warrants
  its first-use source cost.

The archive contains source, reports and receipts only: no compiled
proof objects, binaries, complete repository clone or toolchains.
To rebuild the paper with a standard TeX installation, run `make` or
`pdflatex report.tex` twice. The PDF uses no external images.
