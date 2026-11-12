PACKED-SOURCE ACCOUNTING REVIEW
==============================

The straightforward packed candidate has 18 significant Python tokens,
19 AST nodes and 459 normalized UTF-8 bytes. Its complete fixed payload
recovers the 502-byte checker exactly. The import statements, decoding
calls, execution call and all 395 ASCII payload characters are counted.

THE IDENTICALLY PACKED INCUMBENT HAS THE SAME SIZE.
Applying exactly the same wrapper to the old 506-byte checker also gives
18 tokens / 19 AST nodes / 459 normalized bytes. Both zlib streams have
316 bytes. Consequently packing gives this new refinement NO advantage
over a matched packed incumbent. This is an illustration of the source
accounting boundary, not a new simplification of the mathematical theory.

                                Tokens     AST     Normalized bytes
Expanded incumbent                 267     303                  506
Expanded candidate                 269     301                  502
Packed incumbent                    18      19                  459
Packed candidate                    18      19                  459

The literal packed score falls below the existing direct-source coordinate
envelope (253 / 275 / 506) because the expanded Python syntax resides inside
a counted string literal. Its expanded algorithm still costs 269 / 301 /
502, and the incumbent can be encoded the same way. No axiom, rule or proof
checking operation has disappeared. A representation-invariant metric
would have to specify how encoded programs and generic decoders are charged.

REPOSITORY LANGUAGE ABOUT THIS DISTINCTION
----------------------------------------
I found no explicit project-wide ban on compressed source among the main
project summary and the four inspected incoming packages. I did find this
specific statement in the incoming Orbit report:

  "Removing a printed success signal or embedding a compressed program
  changes the accounting question and does not supply a mathematical
  reduction."

Exact source:
  repository: VladimirReshetnikov/ProveIt
  inspected commit: b1b3ae103314a9668b9f87c76594ecfcc5c177e6
  archive: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/docs/incoming/
           ipra_orbit_closure.zip
  member: ipra_orbit_closure/report.tex
  location: Further research questions, item 4, line 426
  source URL:
  https://github.com/VladimirReshetnikov/ProveIt/blob/b1b3ae103314a9668b9f87c76594ecfcc5c177e6/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/docs/incoming/ipra_orbit_closure.zip

The main ConciseIPRA README, lines 15-22, says the coordinates are normalized
source tokens, AST nodes and UTF-8 bytes, and that "gzip sizes are reported
for information only." This distinguishes ordinary compressed-file size from
the primary metric; it does not expressly specify the treatment of a valid
Python module containing its entire program as an encoded literal.

Research/kernel_refinement/README.txt says its shipped checkers import only
Python's JSON library. That is a description of those programs, not a clear
global eligibility rule. The wrapper below explicitly adds generic zlib and
base64 decoding to the trusted runtime boundary and counts their imports.
It imports no proof-specific module, theorem database, generator or file.

DEPENDENCIES AND EXACT EQUIVALENCE
--------------------------------
The complete outer program is an import of zlib and base64 followed by exec
of a zlib-decompressed, Base85-decoded fixed string literal. The source in
the literal is trusted fixed program data, not certificate-supplied Python.
The proof certificate is still read only by the embedded JSON checker.

Python and its standard libraries are the runtime. Their implementations
are not counted as application source, just as the interpreter and JSON
library implementations are not counted in the direct-source baseline.
All proof-specific source bytes are present within the packed module.
The generic decoder imports are an explicit extension of that dependency
boundary; this fact must not be hidden in a comparison.

The generator verifies byte-for-byte equality of the recovered payload and
the expanded source. The validator independently reconstructs the fixed
outer wrapper, checks that no extra outer statements are present, and
checks payload identity again before executing the checker. The extra
outer exec frame can alter finite recursion-resource limits; the usual
mathematical unbounded-finite-resource reading of the checker is unchanged.

FILES
-----
checker_packed.py             Complete 459-byte packed candidate.
incumbent_506_packed.py       Same wrapper applied to the 506-byte incumbent.
generate_packed.py           Deterministic build helper and identity check.
validate_packed.py           Exact-wrapper/payload and fixture comparison.
metrics.json                 Candidate measurements, hashes and runtime.
incumbent_506_metrics.json    Matched incumbent identity/measurement receipt.
validation.json              Candidate/expanded fixture comparison results.

The build helper is not imported by either checker. It is outside their
trusted checking boundary and is supplied to make the fixed bytes auditable.
Generation used CPython 3.12.14 and zlib 1.3.2. Different zlib compressor
versions can emit different bytes; decompression identity is separately
verified, and the supplied files fix the actual measured representations.

VALIDATION
----------
All 38 inherited fixture files were run through both the packed candidate
and the exact expanded 502-byte source, in ordinary Python and python -O:
152 checker processes, 88 acceptances, 64 rejections, zero mismatches.
No additional incumbent fixture runs were needed: its fixed wrapper and
exact payload identity are verified by the identical generation procedure.
These tests supplement source identity; they do not prove a new arithmetic
metatheorem or solve the requested mathematical minimality problem.

REPRODUCTION
------------
  python3 generate_packed.py EXPANDED.py PACKED.py
  python3 validate_packed.py EXPANDED.py PACKED.py FIXTURE_DIRECTORY REPORT.json

The fixture directory must contain the fixed 38 files and expected.json
from the direct-source package. Neither standalone packed checker needs
that directory, its expanded companion, or any reproduction helper.
