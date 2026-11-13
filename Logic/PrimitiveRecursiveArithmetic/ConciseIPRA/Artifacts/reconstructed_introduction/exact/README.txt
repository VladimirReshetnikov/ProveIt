EXACT-BINDING INTRINSIC THREE-FIELD CHECKER

code/checker.py is the complete standalone counted program.
code/readable.py is an explanatory expansion, not an imported dependency.

Measured with CPython 3.12.14, ast.unparse plus one final LF:
313 significant tokens; 357 AST nodes; 590 UTF-8 bytes; 370 gzip9 bytes.

This one program improves the inspected exact-binding envelope316/358/591.
It does not improve the compact promised-grammar envelope238/255/455 and
does not supply a new arithmetic axiom deletion or a minimality theorem.
The public grammar has actual iterator binding, with JSON True explicitly
permitted as another spelling of numerical-zero code1. Unused JSON payload
is ignored; every actively scanned scalar must be an integer or Boolean.

Run a proof:
  python3 code/checker.py < examples/induction.json

Success prints exactly ACCEPT and a newline. All other outcomes reject.
The input has the goal last; earlier proof packets are consumed from the
end. No certificate-supplied code is executed. Standard JSON is the only
library used by the counted program.

Run the focused verification:
  python3 tests/verify.py

PROOF.txt gives the new checking argument and the precise inherited proof
dependencies. tests/receipt.json records the completed checks; these tests
are supporting evidence, not a replacement for the mathematical argument.

Provenance is pinned to ProveIt commit
e0d702b905c74b74a23d045f8289b151bb8ebcff.
The source_cases and proper_nodes reference come from current incoming
ipra_exact_bindings_2026-11-13.zip. The reference checker316 comes from
ipra_intrinsic_validation_2026-11-13.zip. The fixture translator is the
current validated_phase translator with the actual-binding child-depth
table substituted. All reference code remains attributed to ProveIt.

The new Python source has not been formally verified in Lean or Rocq.
No remote repository was modified.
