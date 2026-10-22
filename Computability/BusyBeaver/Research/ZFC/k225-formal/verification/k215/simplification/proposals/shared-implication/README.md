# K215 proof simplification: shared implication and semantic sites

Baseline: ProveIt commit **2ca3a5c16f0876d2cab842056353c03a1ed2f5f0**. Prepared 21 October 2026.

## Main results

1. **Share the two implication derivations.** Extend the existing 58-step dominated core by five modus-ponens steps for S, export its existing K and Peirce lemmas, and instantiate its guard as True for the unrestricted interface. The two proof files shrink from **819 to 435 lines** and **42,715 to 19,674 bytes**. The combined derivations lose **101 MP steps**. The four-file change, including renderer and derivation data, removes 353 lines and 21,813 bytes.
2. **Make simulation consume semantic site contracts.** The replacement KSim accepts exact instruction contracts independently of a fixed-fuel checker. The old Boolean checker supplies a compatibility adapter. The four old public simulation interfaces keep their original types. A mixed-provider lemma supports migration one primitive family at a time.
3. **Rule out a misleading shortcut.** A checked three-element algebra shows that MP and diagonal-only rho8 instances do not imply unrestricted rho8.

Read **report.pdf** for the mathematical argument, code-level design, Rocq route and integration order. **report.tex** is its complete LaTeX source.

## Verification status

- Lean 4.32.0 checked the full 63-step generic core and exact generic unrestricted adapters: ten named axiom reports, all empty.
- Lean checked the countermodel and universal obstruction: four named axiom reports, all empty.
- The semantic refactor's 13-module project closure and old/new clients passed; final run has 17 compiler invocations.
- The exact same typed legacy client compiled against original and replacement KSim.
- Semantic audits introduce no axioms beyond the existing standard Lean axioms. The semantic halting equivalence uses propext and Quot.sound; its legacy checker wrapper retains Classical.choice.
- The renderer reproduces the new core exactly, existing Nat Lean/Rocq rendering is unchanged, original public basis types are preserved, and the 1,358-byte Tarski suffix is unchanged.
- combined.patch applies cleanly to the pinned checkout.

**Not yet checked:** the complete modified K215 endpoint and the full replacement Lukasiewicz module with its Tarski dependencies. Shared primitive-and-return families remain to be proved. The Rocq interface file is an **uncompiled design draft**. The existing machine, source and endpoint targets are unchanged.

The semantic interface grows KSim from 356 to 482 lines. It is an enabling abstraction; it removes no site outcomes in this packet and carries no endpoint speedup claim.

## Contents

- report.tex, report.pdf — complete report.
- shared-implication/ — replacements, patch, derivation/renderer, standalone proof and verifier.
- semantic-sites/ — replacement KSim, patch, typed audits and verifier.
- countermodel/ — Lean proof, independent Python check and explanation.
- rocq-design/ — uncompiled semantic-interface proposal.
- verification/core/ — raw logs, source/interface controls and compilation receipt.
- verification/sites/ — baseline/replacement logs and compilation receipt.
- verification/controls.json — cross-package facts and limitations.
- source-pins.json — 21 primary source hashes and pinned URLs.
- combined.patch — both independent changes in one patch.
- verify_all.py — focused serial reproduction.
- NOTICE.txt — attribution and provenance.

## Reproduce focused checks

Use a checkout at the exact baseline and an installed Lean 4.32.0 compiler:

    python3 verify_all.py --repo /path/to/ProveIt --lean /path/to/lean

The drivers use only the selected project sources and Init. No Mathlib, compiler download or repository write is performed. They use a POSIX file lock and one compiler worker. Generated objects and fresh receipts go in verification-run/ by default; these are not shipped.

To check patch applicability:

    git -C /path/to/ProveIt apply --check /path/to/combined.patch

The patches are independently reviewable in their respective directories. Application and a complete endpoint rebuild belong to the repository's normal integration process.

For the report:

    sh build_report.sh

## Suggested integration sequence

1. Adopt the shared implication proof and synchronized producer, then rebuild the full affected logic closure.
2. Adopt semantic simulation with the current Boolean provider and rerun the closed endpoint clients.
3. Prove one complete primitive/return family from the exact existing decoder port. Use mixed coverage for that family, preserve full consumed words and positive progress, and measure real compilation costs.
4. Port the same semantic boundary to Rocq; reconcile the already existing normalized source correspondence separately.

The report distinguishes the existing external proof-assistant halting/refutation theorem from the still separate internal PA/ZFC proof-syntax formalization target.

