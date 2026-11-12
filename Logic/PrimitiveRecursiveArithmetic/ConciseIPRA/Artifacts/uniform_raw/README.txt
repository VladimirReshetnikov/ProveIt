UNIFORM INTRODUCTION ON RAW TERMS
================================
Research prepared for Vladimir Reshetnikov, November 12, 2026.

START HERE
----------
paper.pdf is the complete research paper.
paper.tex and equational_predecessor.tex are its editable LaTeX sources.
code/checker.py is the complete new acceptance program.

RESULT
------
The newest incoming raw guarded calculus recognizes literal naming formulas
and chooses their embedded term as a special introduction witness. This
package deletes that exception. Introduction always uses the newest ambient
numerical parameter, or zero in an empty numerical scope. Terms remain raw
scalar iterator terms; there is no computation normalization.

The written proof establishes equality of every open guarded consequence
relation with the unrestricted-witness calculus. Its ordinary realization
is therefore bi-interpretable and equiconsistent with full first-order iPRA.
Both domains are whole, equality is actual, both numerical comparison graphs
are x=y, and both formula composites are preserved.

The key dependency is proved explicitly: the inherited scalar predecessor
can be constructed using only computation, equality, and equation induction.
Equational interpolation removes its Boolean case splits. A uniformly
generated coverage packet then supplies arbitrary names. Proofs are
regenerated under numerical scope extensions; naive weakening of a finished
proof is not assumed.

EXACT MATCHED COMPARISON
------------------------
Complete strict acceptance module       Bytes    Tokens    AST
Incoming naming-exception control        3688      1159     1339
New uniform-introduction checker          3439      1073     1248
Reduction                                 249        86       91

The programs differ only by deleting the witness() helper and replacing
its call by -scope. The exact AST patch is verified by the reproducer.
Measurements normalize with ast.unparse and count the full program.
CPython 3.12.14 reproduces the delivered exact sizes.

SCOPE OF THE CLAIM
------------------
This is a strict mathematical and checker-size simplification of the newest
raw deterministic presentation. It is not an absolute minimum or a record
over all repository interfaces. Other strict presentations, and especially
compact public-goal codecs, remain smaller in absolute size. The incoming
parameter_intro package already uses the newest parameter on full-normal
counter-aware recursor terms; that fixed-witness idea is credited.

New theorems here are written mathematics with independent review and finite
implementation checks. They have not been newly verified in Lean or Rocq.
The upstream Lean project was not rebuilt. A complete executable translator
for arbitrary old proofs is not supplied. The universal predecessor proof
is in the paper, not a fully expanded accepted native certificate.

REPRODUCTION
------------
From this extracted directory:

  python3 reproduce.py
  python3 code/checker.py < code/examples/accepted/universal_coverage_closure.json
  python3 code/checker.py < code/examples/rejected/naive_weakening_changes_selected_witness.json
  pdflatex -no-shell-escape -halt-on-error paper.tex
  pdflatex -no-shell-escape -halt-on-error paper.tex

The second command prints ACCEPT and exits zero. The third prints REJECT
and exits nonzero. Only Python's standard library is required for the
checker and reproduction. PDF compilation uses ordinary TeX Live packages.
No shell escape, network access, or bibliography processor is required.

The verifier input is a JSON object with exactly goal and proof keys.
Terms use 0 for zero, positive integers for de Bruijn bound indices,
negative integers for free parameter levels, [0,t] for successor, and
[n,a,h] for iteration. Equations are [s,t]; D matrices are [B]. The term
update binds one variable, and D binds two. Every output is checked for
sort, scope, and the public formula guard. See the complete grammar and
six inference instructions in Section 2 of the paper.

VERIFICATION
------------
11 accepted and 17 rejected certificates are run in both ordinary and -O
Python: 56 CLI checks, all passing. Additional checks establish the exact
source patch and a certificate that distinguishes the two witness policies.
The accepted examples include the whole universal coverage closure,
specialization at the successor of a compound iterator term, explicit
extraction of S(b)=S(t), discharge with no escaped witness, and a proof
that genuinely uses its progress hypothesis.

All 11 positives are also elaborated with explicit witnesses and replayed
successfully in the frozen unrestricted-witness checker. The old selector
is tested separately on a certificate tailored to the new rule.

The checks are finite evidence. They do not replace the universal proofs.
Exact results are in code/verification.json and code/metrics.json.

CONTENTS
--------
paper.pdf, paper.tex             Research report
equational_predecessor.tex       Complete equational predecessor appendix
code/                           Checker, frozen control, normalized sources,
                                builders, certificates, metrics, receipts
reference/                      Attributed upstream bridge sources and two
                                Lean comparison statements
notes/                          Additional proof and independent audit notes
reproduce.py                    Entry point for verification
CLAIMS.json                     Claims and limitations
PROVENANCE.json                  Snapshot, archive hashes, source identities
SHA256SUMS                      Checksums of the delivered payload
LICENSE-upstream.txt            Preserved upstream MIT No Attribution license

BASELINE
--------
https://github.com/VladimirReshetnikov/ProveIt
commit 9f9545f5ffd9e0392d4a36639503aca12383450a
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The main README and all five ZIP archives present in docs/incoming at
that snapshot were inspected. The current strict control is taken from
ipra_deterministic_introduction.zip, not an older supplied-witness draft.
