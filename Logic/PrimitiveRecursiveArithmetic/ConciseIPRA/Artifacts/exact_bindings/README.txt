ACTUAL BINDING IN A SMALLER EXACT iPRA PRESENTATION
13 November 2026

RESULT AND LIMIT
----------------
The main construction removes administrative binding slots from the compact
native representation. Successor binds nothing; an iterator binds only its
update variable. The existing public sort and scope check then recognizes
exactly the canonical Eq/D grammar, with no additional availability mask.

Complete programs, measured with CPython 3.12.14:

  code/proper_tokens.py   321 tokens / 373 AST nodes / 689 normalized bytes
  code/proper_bytes.py    330 tokens / 383 AST nodes / 627 normalized bytes
  code/proper_nodes.py    333 tokens / 361 AST nodes / 724 normalized bytes

The recommended program is code/proper_bytes.py. Each program improves all
three coordinates of the inspected exact-canonical reference, 581/641/1424.
The recommended program is 56.0% smaller in normalized bytes.

The stronger requested global-frontier result is NOT established. The programs
do not beat the pooled compact extrema 239/255/460 or the weaker sorted-native
envelope 302/340/584. These envelopes are attained by different programs under
different contracts, and they are not universal lower bounds. This is a
representation and checking-protocol improvement; no arithmetic axiom is
deleted and no absolute simplest presentation is claimed.

THEORY AND PROOF STATUS
-----------------------
The ordinary theory is the existing native scalar calculus, bi-interpretable
and equiconsistent with full first-order intuitionistic primitive recursive
arithmetic. Numerical domains are whole, equality actual, and both numerical
composites are the identity graph x=y. Both formula round trips are inherited
from the pinned native/iPRA bridge.

The report states every primitive native axiom/rule, proves the actual-binding
raw interpretation and opening lemmas, explains the universal call-tree
soundness argument and the native proof compiler, and identifies the imported
arithmetic/logic dependencies. There is no new Lean/Rocq verification of Python.
Finite tests support implementation review; they are not substitutes for proof.

QUICK START
-----------
From this directory, run:

  python3 code/proper_bytes.py < verification/actual_binding/examples/bytes_zero.json
  python3 code/proper_bytes.py < verification/actual_binding/examples/bytes_induction.json

Both print ACCEPT. The second proof uses its induction hypothesis. There are
corresponding token and node examples in the same directory.

Each checker reads one complete JSON array. The last element is its closed
public goal; preceding proof packets are consumed from the end. The byte
profile uses four fields per packet, the other profiles use three. Select the
matching example/protocol. Native terms have zero code 1, bound-variable code
3+2j, successor [t], iterator [n,a,h]. Public formulas are [s,t] and [B] for
equality and D; Q is an internal constructor. The actual binders, not padding
positions, determine j.

Acceptance is normal termination printing exactly ACCEPT followed by a newline.
An exception or missing acceptance marker is rejection. Optimized Python -O is
supported: the checkers do not rely on assertions. Ideal finite resources are
the completeness convention; physical recursion/memory limits can reject very
large correct proofs, as in the source controls.

REPRODUCE
---------
  python3 reproduce.py

This checks the delivered files, remeasures their complete sources, recompiles
the 14 native proof trees into all three actual-binding protocols, runs the
independent syntax and process regressions, and checks the legacy-mask family.
It uses only Python's standard library and no network/repository checkout.

Recorded actual-binding validation: 30,456 independent grammar comparisons and
450 isolated normal/-O process runs, with zero failures. The legacy-mask
alternative has a separate 45,124-grammar / 12,000-opener / 764-process receipt;
the token mask profile and call-arity boundary have additional independent
receipts. Diagnostics explicitly distinguish rejected unsound prototypes from
the proposed checkers.

BUILD THE PDF
-------------
  python3 build_pdf.py

This uses an installed TeX system. It can build a private format/font map when
the installed distribution lacks caches; it downloads nothing and changes no
system configuration. With a configured TeX installation, three ordinary
pdflatex passes on ipra_exact_bindings.tex also work.

FILES
-----
ipra_exact_bindings.pdf / .tex  Complete report and editable LaTeX source.
code/proper_*.py              Main, actual-binding complete checkers.
code/checker_*.py             Alternative signed-mask legacy-codec checkers.
verification/actual_binding/  Portable compiler, 14 source proof trees, examples,
                             negative cases and full reproduction script.
verification/signed_mask/    Portable mask checkers and matched controls.
verification/token_mask/     Token-oriented legacy-mask regression payloads.
evidence/                    Measurements, proofs, reviews and receipts.
reference/                   Baseline checkers, full article TeX sources,
                             NativeBiInterpretation identification module,
                             and upstream MIT-0 license.
diagnostics/                 Tiny false-goal attack and explicit warning.
MANIFEST.sha256               Integrity hashes of the supplied files.

The library of reference sources is included for offline audit; the new report
does not need it to compile. The copied Lean identification module is not a
standalone Lean project. The complete dependent formal development remains at
the pinned repository.

SOURCE PIN
----------
VladimirReshetnikov/ProveIt
e88ebf229bb61bd870bb229b9c97caaa1e044e6e
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

All seven incoming archives at that revision were inspected. A later head check
at 0912ac9bc70397af1ca9c175bd0732132be5eb7b found only four added Lean modules,
with no checker changes. Source-derived material retains the ProveIt MIT-0
license supplied in reference/.
