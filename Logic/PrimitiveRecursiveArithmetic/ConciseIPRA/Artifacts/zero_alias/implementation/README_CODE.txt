ZERO-ALIAS CHECKER ARTIFACTS

Main complete checker: alias_inverted.py
Readable independent expansion: checker_readable.py

The main checker measures 331 significant Python tokens, 373 AST nodes and
625 normalized UTF-8 bytes under CPython 3.12.14. After inspecting all thirteen incoming archives, the strict-family
envelope is 334 / 386 / 628, attained by three different programs. The new
program is below all three of those coordinates. It does not beat the
478-byte compact checker, which has a different validation contract.

The public constant c is encoded by the numerical atom 1. The initial
auxiliary context includes c=0, encoded [1,0]. Numerical zero in computation
and instruction fields remains the raw integer 0. Thus wholesale replacement
of every 0 in a certificate by 1 is NOT a correct proof translation.

The public arity grammar and the exact integer/list alphabet throughout
the input are validated. Completeness is stated for the canonical encoding
of named formulas. The inherited arity grammar also admits references to
artificial constructor slots; this package does not assert completeness
for every such noncanonical spelling. Unused certificate prefixes are
permitted, but their types are still checked.

RUN

  python3 alias_inverted.py < fixtures/generated/zero_computation.json
  python3 checker_readable.py < fixtures/generated/nested_D_transport.json
  python3 compile_alias.py
  python3 verify_alias.py

The examples print ACCEPT. Exceptions reject. The compiler is untrusted;
neither checker imports it or any vendored proof-producing dependency.

The compiler constructs formula transport from 0=c under the fixed c=0
hypothesis, recursively through D binders. Its seven positive certificates
exercise computation, equality, induction with a used hypothesis, nested
binders, and nonvacuous witness discharge. The named producer and transport
normalizer under ref/source_dispatch are exact, attributed upstream files.

The delivered verification receipt has 51 candidate cases, each executed
on both implementations in ordinary and optimized Python (204 runs), with
zero failed expectations. It also replays all 121 inherited cases against
their original, unchanged controls in both modes (242 runs), with zero
failures. The two additional no-alias control runs correctly reject the
translated zero-computation certificate. No finite suite proves the
universal metatheorems; the mathematical arguments are in the report.

PROVENANCE.json pins every included reference file to ProveIt commit
f2e1d0f2d29042fa2d76244639c13425c46d16b4. All 146 reference Git blob hashes
were verified. verification.json records exact metrics, the structural AST
audit of the documented transformations, and every execution result.

The new code may be used under the same MIT No Attribution license as the
included upstream sources; see LICENSE-upstream.txt.
