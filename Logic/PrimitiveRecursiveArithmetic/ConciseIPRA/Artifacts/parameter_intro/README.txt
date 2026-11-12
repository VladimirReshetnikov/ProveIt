iPRA WITHOUT SUPPLIED INTRODUCTION WITNESSES
==========================================
Prepared for Vladimir Reshetnikov, November 11, 2026.

START HERE
----------
ipra_parameter_intro.pdf is the full mathematical report.
ipra_parameter_intro.tex is its complete standalone, editable LaTeX source.
code/checker.py is the entire selected acceptance program.
code/checker_normalized.py is the exact 1925-byte normalized module.

RESULT
------
There are three inference families: clause Use, paired Introduction, and
equality Substitution combined with witness Discharge. The only fixed
axiom clause is universal reflexivity. Introduction receives no witness:
it uses the newest outer numerical parameter, or zero at the closed root.
The theory has one counter-aware successor-seeded recursor and equations
and a paired binder D as its formula constructors. Full computation
normalization belongs to the syntax and is included in the checker.

The naming theorem recovers arbitrary existential witnesses through
clause specialization. The relative proof translation handles the fact
that adding a numerical parameter changes the newest witness. It uses
persistent assumption builders, not an unjustified target weakening rule.
The ordinary realization is equiconsistent and bi-interpretable with full
first-order intuitionistic primitive recursive arithmetic. Both numerical
domains are whole, equality is actual, both comparison graphs are x=y,
and both formula composites are provably the identity up to equivalence.

A second theorem removes a redundant template-scope traversal: both
normalized endpoint formulas remain checked, and any accepted auxiliary
template can be completed to a legal canonical one with those same endpoints.

MEASURED REDUCTION
------------------
Complete module                       Bytes  Tokens  AST
New selected checker                   1925     630  701
Matched supplied-witness control        1967     636  707
New, with template prevalidation        1985     646  717
New finite-fuel checker                 2056     667  748
Incoming explicit Name                  2010     636  708
Incoming inferred opening              1990     683  771

Measurements count the complete standalone acceptance module after
ast.unparse normalization on CPython 3.12.14, with documentation removed
and one final LF. The witness-interface change alone saves 42 bytes,
6 tokens, and 6 AST nodes against its matched control.

This is not a proof of absolute minimality. The repository's compact
508-byte, 256-token, and 276-AST profiles (different programs), and its
780-byte native public-goal profile, remain smaller. Their proof protocols
and input contracts differ. The new module improves all three coordinates
against the two selected recent strict implementations.

The new metatheorems are written mathematics, not newly checked Lean or
Rocq proofs. The source Lean files included here are attributed comparison
statements, not a complete new Lean project. Full normalization is not
claimed uniformly primitive recursive; checker_fuel.py supplies a bounded
finite-certificate relation with the same theorems when sufficient fuel
is provided.

REPRODUCTION
------------
  python3 reproduce.py
  python3 build_pdf.py
  python3 code/checker.py < code/examples/name_one_without_witness.json

The checker and evidence scripts use only Python's standard library.
Python 3.10+ supports the syntax; exact delivered metrics use 3.12.14.
The PDF build requires pdfLaTeX with ordinary TeX Live packages.
It runs with shell escape disabled. All code paths are relative to the
package; no external service is needed for reproduction.

The main certificate is [goal, proof]. The bounded certificate is
[goal, proof, fuel]. Acceptance means zero process exit status and
exactly ACCEPT followed by a newline. Unconditional clause-use instructions
have no premise; their unused payload is conventionally null.
See code/README.txt for all syntax and instruction details.

VERIFICATION
------------
13 accepted examples; 23 rejected attacks; 13 translations to the
explicit-witness control and 13 to the template-validation control;
140 actual normal/optimized CLI runs; 26 exact/one-short fuel checks;
8 malformed budgets; 400 oracle normal forms, 1200 numerical comparisons,
480 openings, 320 contractions, and 2 capture controls. All passed.
The independent template-completion experiment checks 5000 templates,
including 109 valid instances with erased extra parameters. No mismatch.
Finite experiments supplement the universal written proofs.

CONTENTS
--------
ipra_parameter_intro.pdf/.tex  Complete report and standalone LaTeX
front.tex, core.tex, etc.      Editable component sources used to assemble it
code/                         Checkers, matched controls, test producers,
                              oracle audits, and generated certificates
evidence/                     Exact measurements, replay and build results
reference/                    Pinned upstream sources and license
CLAIMS.json                   Explicit result and limitation ledger
SOURCE_PROVENANCE.json        Source identity and reference hashes
SHA256SUMS                    Hashes of all other package files

SOURCE SNAPSHOT
---------------
https://github.com/VladimirReshetnikov/ProveIt
commit 11814771b7490dfbea0ed5fcf0f5b23586334764
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
All 73 filed-package summaries and six current incoming packages were
considered; the relevant definitions, checker sources and bridges were read.
The existing MIT No Attribution license is retained for upstream material.

NOTATION IN THE INHERITED FOUNDATION FILES
----------------------------------------
The short new left inverse P(n)=R(n,0;i,u.i) has P(0)=1 and P(Sn)=n.
When the inherited equality-reflection text writes P for a predecessor
with P(0)=0, use p(n)=C(n,0,P(n)) from the present report.
