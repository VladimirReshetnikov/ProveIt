INCIDENTAL SOURCE-SIZE RECORDS FOR THE EXISTING iPRA CHECKER
==========================================================

This folder contains five complete standalone variants of the current
generated-assumptions checker, plus its two frozen baseline implementations.
All variants recognize the same inherited certificate language. They do not
implement the new fixed-counter mathematical calculus, add arithmetic axioms,
change induction, or establish a significant structural breakthrough.

The improvements are ordinary Python import, exact-type predicate and
control-flow spellings. Their whole-program costs are:

  file                         normalized tokens    AST nodes    bytes
  reference/baseline.py               281              318        685
  reference/baseline_ast.py           283              315        710
  import_json.py                      281              320        680
  exact_class.py                      280              321        680
  exact_type.py                       281              322        676
  zero_product.py                     281              322        672
  ast_not_in.py                       283              314        751

The pinned current corpus envelope was 281 / 315 / 685. The selected
collection improves it to 280 / 314 / 672, with different programs attaining
the coordinates. No selected single program is strictly below all three old
coordinates. The token and AST gains are one each; the byte gain is thirteen
(about 1.90%). These are implementation records, not a new arithmetic basis,
absolute simplestness result, or claim that cryptic syntax is easier to read.

What the variants change
------------------------
import_json.py imports the module and calls json.load instead of importing
load directly. Every proof-checking and substitution byte is unchanged.

exact_class.py and exact_type.py additionally replace isinstance(a,list)
with a.__class__ is list or type(a) is list. The complete program's ordinary
JSON decoder and its own constructors create only exact built-in values,
so no list subclass creates a distinction. No custom JSON hooks are used.

zero_product.py instead tests a*0 == []. For exact lists this is true.
For numeric values and strings it is false. Dict and None inputs raise
earlier, but the old decoder invariably raises on its scalar comparison
for those same inputs. There is no inner recovery handler. Thus accepted
certificates and successful values are unchanged, though rejection tracebacks
can differ. PREDICATE-EQUIVALENCE.txt gives the complete runtime-type argument,
including NaN/infinities and physical-resource qualifications.

ast_not_in.py starts from the frozen AST profile. It replaces the early-return
membership branch with one inverted nonmembership guard around the complete
remaining function body. Explicit and implicit return both produce None;
the same opener is evaluated once. The Return AST node disappears, while
extra indentation increases the normalized byte count. See
GUARD-EQUIVALENCE.txt for the exact correspondence.

All changes rely on the specified standard Python/JSON runtime, as do the
original checkers. They are not claims about arbitrary custom Python objects
injected into a separately exposed helper. Programs accept JSON data only;
no submitted Python or theorem-specific dependency is loaded.

Portable reproduction
---------------------
From this folder, run:

    python3 verify.py

The verifier needs only Python's standard library and relative package paths.
When this folder is delivered as ancillary/ inside the main report archive,
it measures with ../reference/source_measure.py. An identical frozen copy in
reference/source_measure.py is the fallback when this folder is copied alone.
The verifier checks normalizer identity before use. Recorded numbers use
CPython 3.12.14; metrics.json also records the actual interpreter version and
whether its profiles match those recorded here.

Every complete variant and both baseline programs run on all 28 inherited
witness certificates (14 positive, 14 negative) and three malformed input
payloads, under ordinary Python and -O: 434 total standalone runs, including
310 candidate runs. Every verdict and exit status must match the unchanged
baseline. Diagnostic exception messages are not compared.

Three targeted guard deletions are checked for each variant (15 controls).
The actual program must reject the selected invalid certificate, while the
guard-deleted program must accept it. Temporary mutants are removed after
the test. Finally 57 deterministic opener states compare all seven programs
on every JSON runtime class, numeric aliases, NaN/infinities, nested malformed
nodes and scope boundaries. These tests supplement the equivalence arguments;
they do not prove the inherited theory's metatheorems or verify Python itself.

Files
-----
The five top-level candidate .py files are complete independent checkers.
verify.py is an untrusted evidence runner and is never imported by them.
reference/ contains unchanged baseline sources, unchanged source measurement
code, and the inherited MIT No Attribution license.
witness_cases.json is the unchanged inherited fixture suite.
malformed_inputs.json records the three additional input failures.
PROVENANCE.json records the pinned archive/member identities and payload hashes.
metrics.json records complete-module measurements, not uncharged fragments.
validation.json records all verdict pairs and mutation controls.
opener_validation.json records the 57 independent type/scope situations.

Inherited source: VladimirReshetnikov/ProveIt, commit
2fdcf5bf988bead821c416649f713f98b7ed8776,
docs/drafts/ipra_generated_assumptions_2026-11-10.zip.
The inherited mathematical soundness argument is a written proof; neither
these source changes nor their finite tests are a new Lean/Rocq formalization.
