iPRA: A SMALLER CHECKER AND TWO STRUCTURAL BARRIERS
Prepared for Vladimir Reshetnikov, November 10, 2026.

RESULT AND LIMIT

This package obtains a modest complete-checker reduction and two additional
mathematical obstructions. It does NOT establish an absolute simplest
axiomatization, the requested significant positive breakthrough, or a single
program strictly below all current source-coordinate minima.

The underlying scalar-iterator Choice-DI axiomatization and its full-domain
bi-interpretation with iPRA are inherited and explicitly attributed. Every
logical/nonlogical primitive and the complete inherited bridge are included.
The implementation composes the existing arity codec and uniform-predecessor
protocol. The source comparison is pinned to ProveIt commit
fb2dbd2a33c6b132671a54b029d0bf3cd98c633d, docs/drafts.

COMPLETE CHECKERS (CPython 3.12.14; gzip uses zlib 1.3.2)
                                      bytes  tokens  AST  gzip-9
Existing observed coordinate minima    616     268   300   --
implementation/checker_explicit.py     612     266   310   360
implementation/checker.py              604     266   312   356
implementation/checker_short.py        593     267   315   355
implementation/checker_guarded_ast.py  690     269   300   371

Different old programs attain the old minima. The explicit-list profile is
recommended for inspection. The short profile uses inherited Boolean idioms.
The guarded AST profile matches the old AST minimum while rejecting strings
immediately. All four terminate structurally on finite JSON inputs, subject
to ordinary physical resource limits.

Fair control: old arity compact source with the same driver is 608 bytes,
265 tokens, 314 AST. The 604-byte composition saves 4 bytes and 2 AST nodes,
but costs 1 token. Do not attribute driver changes to new mathematics.
Gzip is informational; full raw/normalized measurements are in
implementation/metrics.json, with exact compressed files beside each checker.

ADDITIONAL MATHEMATICAL RESULTS

1. Progressive-binder Boolean-case obstruction. For
   H_xy B = exists x forall y (B(x,y) -> B(x,Sy)),
   F(t) = H_uy H_vz (C(t,Z(y),z)=0)
   is provable at 0 and 1 in the case-free calculus but false at mixed
   parameter (0,1) in N^2. The product validates all remaining rules,
   including equation induction with arbitrary parameters. This directly
   refutes deletion of Boolean cases from the existing progressive theory.

2. Exact positive-iteration zero profiles. For terms built only from
   variables, 0, S, and R+(n,a;h)=h^(n+1)(a), the zero set is empty, universal,
   or one coordinate zero hyperplane. Thus predecessor, zero-test, ordinary
   addition, and initialized iteration are not term-definable. This does
   not exclude arbitrary relational or changed-domain interpretations.

READ FIRST

report.pdf                     Complete typeset report.
report.tex                     Modular main source.
report_standalone.tex           Fully expanded source, including checker listing.
theory/                        The two additional obstruction proofs.
reference/                     Attributed complete inherited iPRA bridge.
implementation/                Complete checkers, producer, fixtures, controls.
code/                          Corpus census and independent math diagnostics.
evidence/                      Inventories, hashes, runtime, reviews, results.
CLAIMS.json                    Exact claim and limitation ledger.
MANIFEST.json                  Payload hashes and sizes.

REPRODUCE

    python3 reproduce.py
    python3 build.py
    python3 build.py --standalone

The first command verifies payload hashes and runs finite checks in a temporary
copy. Python uses only its standard library. The build commands require an
installed TeX distribution with the packages listed in report.tex. Rebuilding
can change PDF metadata and therefore the distributed manifest hash.

    python3 implementation/checker_explicit.py < implementation/fixtures/I0_arbitrary_seed.json

Success requires exit 0 and exactly ACCEPT plus newline. Exceptions reject.
Certificates are JSON data, never executable input. The untrusted example
producer is not a general compiler from arbitrary ordinary-iPRA proofs.

RECORDED VALIDATION

416/416 complete CLI checks passed (42 certificates + 10 malformed inputs,
four profiles, normal and -O Python); 8/8 targeted mutation controls passed.
55,443 generated arithmetic equation valuations and 216 independent binder
comparisons passed with no evaluation skips. The independent zero-profile
diagnostic checked 2,868 terms at 45,888 valuations, with no skips/mismatches.
The separator script illustrates its explicit product witnesses.
These are finite checks, not proof-assistant verification of the metatheory.

The full source census contains 13 active ZIPs, 28 distinct archives after
recursive traversal, 1,383 Python occurrences, 370 distinct source hashes.
code/audit_corpus.py repeats it when supplied the pinned docs/drafts directory.
Original archives are not recursively duplicated in this package.

No repository commit, pull request, or publication was made.

ADDITIONAL SAME-DRIVER AUDIT

Screening 105 old complete-program profiles under the same rejection driver
finds a 601-byte affine control (274 tokens, 318 AST, gzip 358). The new
593-byte profile saves eight bytes, about 1.33 percent, against that stricter
minimum. The 604-byte and 612-byte profiles do not beat it. Matched token
and AST minima are 264 and 297 and remain unbeaten by the new family.
The exact affine source and transformed control are included.
