EXACT CANONICAL BINDING MASKS: REPRODUCTION

Run python3 verify.py under CPython 3.12.14. No network or repository checkout is required. The script uses only Python standard-library modules. It reproduces exact-source measurements, 45,124 comparisons with the upstream exact canonical predicate, 12,000 proof-phase opener comparisons, and 764 isolated normal/-O process runs against matched canonical wrappers. The controls/ directory is regenerated from the supplied unchanged source cores and exact predicate. Finite tests supplement the written mask invariant; they do not prove arithmetic bi-interpretability.

exact_bytes.py: 365 tokens / 430 AST nodes / 696 normalized bytes.
exact_ast.py: 368 tokens / 408 AST nodes / 793 normalized bytes.
The upstream complete exact-syntax reference is 581 / 641 / 1424. The new checkers use the same ordinary native calculus and canonical goal language, with different compiled proof packets from the older reference. Each matched wrapper uses precisely the same proof packets as its new checker.

The entire parsed JSON alphabet is checked, including unused entries. The public goal is exactly a canonical closed native Eq/D formula. Acceptance is normal termination with exactly ACCEPT followed by a line feed; exceptions reject. Completeness uses ideal finite resources. Do not run with a modified Python interpreter or substitute the deliberately unsound diagnostic for a checker.

reference/ contains attributed controls and inherited fixture payloads. REFERENCE_PROVENANCE.json records their hashes and pinned provenance. diagnostics/ is a deliberately unsound rejected prototype with a tiny 0=S0 attack, included only as an explicit negative control.
