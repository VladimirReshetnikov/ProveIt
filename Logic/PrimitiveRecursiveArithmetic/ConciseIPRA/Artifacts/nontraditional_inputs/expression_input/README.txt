INTEGER/LIST EXPRESSION INPUT FOR THE EXISTING iPRA CHECKERS
=========================================================

Result: three smaller complete source modules under a changed, fully checked
certificate-reader contract. This is an implementation-only partial result.
No arithmetic or logical primitive is removed. The compact frontier and the
request for a new mathematical axiomatization below every record remain open.

Complete programs, CPython 3.12.14 normalized tokens / AST nodes / bytes:

  code/checker_tokens299.py      299 / 350 / 632  (control: 302 / 352 / 646)
  code/checker_ast338.py         311 / 338 / 667  (control: 314 / 340 / 681)
  code/checker_bytes575.py        308 / 358 / 575  (control: 311 / 362 / 584)

Different programs attain the envelope 299 / 338 / 575. All three are smaller
than their own control in every measured coordinate. No single program beats
all old coordinate minima; none beats the compact 239 / 255 / 460 envelope.

The input reader admits only ASCII digits, -, [, ], comma, and JSON whitespace.
After checking that whole text alphabet, it evaluates the resulting restricted
integer/list expression. It can evaluate subtraction and list subscripts, but
cannot express identifiers, calls, attributes, or other executable operations.
The complete measured program enforces this restriction before evaluation.
An exception is rejection; acceptance is normal exit with exactly ACCEPT LF.

The three inference kernels are AST-identical to the corresponding incoming
scope_phase programs at repository snapshot e88ebf229bb61bd870bb229b9c97caaa1e044e6e.
Only the reader/import code changes. The source syntax is new; it is not the
same JSON contract. The mathematical correspondence concerns the parsed data
and represented canonical theorems, with arbitrary finite parser resources.

Actual CPython eval has a stricter nesting limit than json.loads. The new reader
therefore has a practical depth limitation in addition to the inherited stack,
memory, and integer-conversion limits. The exact limitation and a reproducible
example are recorded in proofs/reader_theorems.txt and evidence/runtime_limits.json.

The inherited small public validator recognizes sorted syntax, which includes
some noncanonical padding-slot aliases. Completeness holds on canonical
encodings, not every admitted alias; this is unchanged. No exact canonical-image
validation or new Lean/Rocq verification is claimed.

Reproduce:

  python3 verify.py
  python3 translate.py < valid_old_certificate.json > expression_certificate.txt
  python3 code/checker_tokens299.py < expression_certificate.txt

Use the translator only with the corresponding old protocol. The token/AST
profiles have different freshness schedules and do not share arbitrary input
certificates. The byte profile has four fields rather than three.

verify.py replays all 287 inherited fixture cases against controls and candidates
normally and with -O, verifies unchanged kernel ASTs, tests 42 translator round
trips, and tests new expression spellings and prohibited syntax. The recorded
run contains 1454 isolated processes with zero unexpected outcomes. These finite
tests support the written universal reader proof; they are not its replacement.

The untrusted translator and verification scripts are conveniences. None is
imported by a measured checker. The entire measured module is present in code/.
Upstream adaptations retain the supplied MIT No Attribution license.
