A SHARED-LEAF PRESENTATION OF iPRA
Prepared for Vladimir Reshetnikov, 12 November 2026
================================================

OPEN FIRST

  ipra_shared_leaf.pdf
  report.tex + new_proofs.tex

RESULT

The current compact coordinate envelope is improved from

  243 significant Python tokens / 264 AST nodes / 474 normalized bytes

to

  242 significant Python tokens / 262 AST nodes / 469 normalized bytes.

These three minima are attained by DIFFERENT complete standalone programs.
No single program has vector 242/262/469. This is a small reduction in the
checking presentation, not a new arithmetic axiom deletion or a theorem
of global minimality. Both iterator computation equations remain axioms.

The shared leaf makes one generated computation equation available during
hypothesis lookup. A goal closes if it is either retained or that equation.
Every hypothesis call now consumes a harmless dummy packet. The report
proves context- and height-preserving equivalence on every open sequent.
The inherited full intuitionistic first-order iPRA bridge is unchanged:
both domains are whole, equality actual, and both comparison graphs x=y.

COMPLETE MEASURED PROGRAMS

                          tokens   AST   normalized bytes   gzip level 9
  code/checker_tokens.py     242    268          565              331
  code/checker_ast.py        246    262          556              335
  code/checker_bytes.py      272    306          469              309

Normalization: CPython 3.12.14 ast.unparse of the whole module plus one LF.
Gzip compresses that normalized source with compresslevel=9 and mtime=0.
The corresponding .py.gz files are included. Source hashes and runtime
details are in evidence/metrics.json. Each measured program is standalone;
none imports a project module, table, compressed program or proof compiler.

INPUT CONTRACTS -- KEEP THESE CATEGORIES SEPARATE

The compact profiles assume finite exact-integer/list certificate trees
and a canonical closed guarded Eq/D public goal. They check proofs and
scope but do not validate the whole promise on arbitrary JSON.

checker_tokens.py and checker_ast.py take JSON lines: the public goal on
the first line, followed by one three-field instruction per line. Their
instruction streams differ because the AST profile explicitly checks its
neutral major. Use the matching fixtures/ directory or translator.

checker_bytes.py takes one JSON array: four-field packets followed by
[goal,0]. It consumes the array backwards. Its dummy hypothesis packet
is [[],0,0,0]. The readable standalone expansion uses the same protocol.

Success for every checker is normal exit and exactly ACCEPT followed by
one LF. Exceptions and resource exhaustion reject. An unused certificate
prefix/suffix is allowed according to the profile's reading direction.
Theorem-set completeness uses the usual unbounded mathematical execution
model; an actual Python process has memory and recursion limits.

code/strict_incumbent616.py is the UNCHANGED 616-byte current strict
companion from the abstraction_and_refinements incoming package. It
validates the complete alphabet and the native Eq/D public grammar and
uses its own inherited certificate protocol. It is not one of the new
compact records and not claimed to be improved here. Strict examples are
under fixtures/strict/.

RUN EXAMPLES

  python3 code/checker_bytes.py < fixtures/bytes/guarded_induction_with_used_hypothesis.json
  python3 code/checker_tokens.py < fixtures/tokens/global_shared_computation.jsonl
  python3 code/checker_ast.py < fixtures/ast/global_guarded_induction_with_used_hypothesis.jsonl
  python3 code/strict_incumbent616.py < fixtures/strict/compound_implication_elimination_local.json

REPRODUCE

  python3 reproduce.py --manifest-only
  python3 reproduce.py
  python3 reproduce.py --pdf

Python checks use only the standard library and no network. PDF compilation
needs the installed TeX packages named in report.tex. The supplied helper
can generate a private format and font map from installed TeX sources if
the system caches are absent; it does not download dependencies or modify
the system installation.

Reproduction writes fresh evidence files and optional PDF bytes. Environment
metadata or PDF timestamps can therefore alter the manifest afterward.
Check the manifest before regenerating files, or reproduce in a copy.

VERIFICATION

The packaged suite completed 174 isolated normal/-O executions with no
unexpected outcome, and reproduced 21 certificate translations exactly.
The fixtures include genuinely used induction, compound logical elimination,
shared computations, transport, false conclusions, and scope/context attacks.
The explicit future-witness attack fails at old-scope validation, not merely
because a newly required dummy packet was omitted.

Universal claims have written mathematical proofs and independent in-run
reviews. Finite tests are supporting evidence, not universal soundness proofs.
The upstream Lean bi-interpretation theorem source is included but its
dependency tree was not recompiled. There is no new Lean/Rocq formalization
of the Python correspondence in this package.

CONTENTS

  report.tex, new_proofs.tex, ipra_shared_leaf.pdf
      Complete theory, proofs, interpretation details, comparison and limits.
  code/
      Three record modules, normalized gzip copies, readable expansion,
      untrusted translators and unchanged strict companion.
  controls/
      Exact current compact controls from computation_leaves.
  fixtures/
      Current-source and translated proofs plus negative controls.
  measure.py, verify.py, reproduce.py, census.py, pdf_build_support.py
      Reproducible measurements, checks, corpus audit and PDF construction.
  evidence/
      Metrics, 4,942-path source census, test ledgers, build and layout QA.
  review/
      Independent mathematical and implementation review notes.
  reference/
      Exact attributed upstream theorem and chapter sources. Chapter
      fragments are reference dependencies, not standalone TeX documents.
  PROVENANCE.json, CLAIMS.json, MANIFEST.sha256, LICENSE.txt
      Source identities, precise claims, full checksums and MIT-0 license.

PINNED BASELINE

  https://github.com/VladimirReshetnikov/ProveIt
  Commit 12197d86f63e9ec73b2d91399c4de2a8cb0077ee
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

All five incoming archives in that snapshot were considered. The census
measured 4,942 .py/.py.gz paths and 1,788 unique source contents; it excludes
separate recounting of extensionless historical source stores. The current
three control modules are the strongest direct-source compact thresholds
found under the documented comparison. Compressed execution wrappers and
the stricter validation interfaces are separate accounting categories.

No remote repository mutation, commit, pull request or publication was made.
