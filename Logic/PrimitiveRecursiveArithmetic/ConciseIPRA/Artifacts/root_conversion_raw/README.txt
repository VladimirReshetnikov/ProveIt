ROOT CONVERSION AND FINITE TABLES FOR INTUITIONISTIC PRA
Prepared for Vladimir Reshetnikov, 12 November 2026

RESULT AND LIMIT
===============
The new seven-rule calculus uses raw counter-aware primitive recursion,
variable-only substitution, and reversible conversion at the ROOT of one
equation endpoint. A three-row table recovers arbitrary term transport.
No normalizer and no search inside a recursor counter are needed.

The paper proves equivalence with the full raw counter-aware native kernel
on every open sequent. Its ordinary realization is equiconsistent and
bi-interpretable with full first-order iPRA: whole numerical domains,
actual equality, and both numerical comparison graphs x=y.

This is NOT a solution of the stronger global all-coordinate size target.
The new strict checker is smaller than its matched scalar BH3 control,
but larger than the compact records. A separate refinement of the existing
scalar checker improves ONLY its byte record from 477 to 476.

                          tokens    AST    normalized bytes    gzip-9
New root-conversion        1029     1096         3003             1067
Matched scalar BH3         1056     1127         3089             1086
Separate compact            274      306          476              312
Incoming compact envelope   244      265          477             varies

The envelope is attained by DIFFERENT programs; it is not one checker.
These are achieved upper bounds, not proved absolute lower bounds.
The 476-byte program implements the inherited scalar guarded calculus,
NOT the new counter-aware calculus.

START HERE
==========
ipra_root_conversion.pdf   Complete report and proofs.
ipra_root_conversion.tex   Self-contained editable LaTeX source.
native/FORMAT.txt         Exact new certificate syntax and inference rules.
compact/PROOF.txt         Exact local checker refinement and input contract.
CLAIMS.json               Machine-readable boundaries of the claims.

RUN AND REPRODUCE
================
Python standard library only. Measurements use CPython 3.12.14.

  python3 native/code/root_checker.py < native/tests/transport_symbolic.json
  python3 native/code/verify.py
  python3 compact/verify.py
  python3 build_report.py

The first command checks an OPEN SEQUENT with two hypotheses. A theorem
certificate has an empty context. The full input object is explained in
native/FORMAT.txt. Successful checking prints exactly ACCEPT and exits zero.

The compact program instead assumes a canonical closed guarded scalar
Eq/D goal and exact integer/list trees. It reads one JSON array ending
in [goal,0], with preceding four-field instruction records consumed from
right to left. It is not a validator of arbitrary JSON or public syntax.
Use its own fixtures and converter; native and compact inputs differ.

VERIFICATION
============
Native: 29 fixtures, 58 isolated CLI runs, including Python -O, all pass.
The symbolic transport proof is 4268 bytes and uses 18 root conversions.
Compact: 66 fixtures x 3 programs x normal/-O = 396 CLI runs, all pass.
An independent review checked the proof order, zero-witness edge case,
simultaneous substitution, and a nested counter/state boundary example.

These finite checks support implementation correctness. The universal
equivalence and bi-interpretation are written mathematical arguments.
No new Lean/Rocq formalization or compiled proof-assistant proof is claimed.
Existing Lean reference files were inspected, not rebuilt.

PACKAGE
=======
native/      Full new checker, producer, fixtures, matched control, receipts.
compact/     476-byte refinement, readable expansion, fixtures, control, proof.
evidence/    Baseline census, final package verification, independent audit.
reference/   Pinned inherited bridge chapter and Lean endpoint.
build_report.py
             PDF build helper, with a local installed-TeX fallback.
MANIFEST.sha256
             Integrity ledger of the distributed files except the ledger.

The reference bridge chapter is a source excerpt from the integrated book
and is not separately compilable. NativeBiInterpretation.lean retains its
upstream imports and is not a standalone new Lean project. Neither is a
runtime dependency of a checker.

PROVENANCE
==========
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 31e1e9220868788a85ca5fea351d7ab4097cfa4a
Subtree: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
The new mathematical contribution is the root-only finite-table transport
argument on raw counter-aware terms. Naming packets, the native Q/D
interface, counter-aware term languages, and the inherited iPRA bridge
already occur in the repository and are explicitly attributed in the paper.

Inherited and new material is distributed under the included MIT-0 license.
No GitHub repository files were changed, committed, or published.
