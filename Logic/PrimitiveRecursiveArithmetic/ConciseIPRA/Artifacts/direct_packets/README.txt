Smaller proof presentations of iPRA
=================================

Prepared for Vladimir Reshetnikov, 12 November 2026.

Read report.pdf (or its complete source report.tex) first.

RESULT
------
At ProveIt commit c2e762c43a39ae3757a1208b333e97df056085f8, including all
nineteen incoming archives, the compact whole-JSON coordinate envelope was
248 significant Python tokens / 268 AST nodes / 469 normalized UTF-8 bytes.
The three new whole-JSON modules give 246 / 263 / 465, attained by different
programs. The JSON Lines companion has 259 AST nodes, versus the prior 262.

Program                             Tokens  AST  Bytes  gzip-9
code/checkers/checker_tokens_json.py   246   273   565    339
code/checkers/checker_ast_json.py      258   263   595    356
code/checkers/checker.py               274   303   465    307
code/checkers/checker_ast_jsonl.py      252   259   595    349

All sizes charge the entire standalone module. Normalization is
ast.unparse(ast.parse(source)) plus one LF on CPython 3.12.14; gzip has
compression level 9 and mtime 0. The .gz files are distribution copies of
normalized source, not executable wrappers or a different complexity claim.

WHAT THIS DOES NOT CLAIM
-----------------------
The arithmetic/logical axioms are unchanged. This is a proof-presentation
improvement of the established guarded scalar calculus, not a new axiom
deletion or mathematical breakthrough. No one program is below all three
prior coordinate minima. The mixed-framing token record remains 241.
The stricter native-goal and whole-alphabet-validation records are not
improved. No absolute minimality or new Lean/Rocq checker formalization is
claimed. If the request requires a new mathematical axiomatization below
the entire frontier, that stronger target remains unmet.

THEORY AND PROOF STATUS
-----------------------
The report gives all terms, formula formation rules, six primitive rule
families of the measured calculus, freshness conditions, and the guarded
public grammar. It gives the ordinary reading, the inherited logical
macros, the arithmetic interpretation maps and round-trip dependencies.
The byte, AST and framing changes have written successful-run simulation
proofs. These preserve the public theory and transfer its existing full
first-order iPRA bi-interpretation and equiconsistency unchanged.

The compact input promise remains: a canonical closed guarded Eq/D goal,
finite exact-integer/list proof data, and the specified framing. These are
not arbitrary-JSON-validation programs. Exceptions reject. Resource limits
may reject valid large proofs; the proofs concern ideal finite execution.

CONTENTS
--------
report.tex, report.pdf       Full report and compiled PDF.
measurements.tex            Automatically generated complete-module table.
validation.tex              Executed-check summary used by the report.
CLAIMS.json                 Machine-readable claims and explicit limits.
PROVENANCE.json             Pinned repository, source paths and SHA256 hashes.
code/checkers/              Four selected checkers, exact controls, readable
                            expansion, translators, focused verification,
                            fixture certificates and recorded results.
evidence/                  Full baseline census and contract-specific minima.
evidence/independent_review/ Separate review of scope, framing and pattern failure.
reference/chapters/         Exact attributed mathematical reference sources.
reference/lean/             Exact source excerpts identifying bridge theorems;
                            not a standalone Lean project or a new Lean proof.
tools/census.py             Rebuild the static census from a local repository.
reproduce.py               Remeasure complete modules and run the focused checks.
SHA256SUMS                 Hashes of archive contents, excluding this hash file.

REPRODUCTION
------------
Use CPython 3.12.14 for exactly the recorded AST and bytecode conventions:

    python3 reproduce.py

The test suites also run the checkers with -O; no checker depends on assert.
To compile the report:

    latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

To reproduce the baseline census, check out the pinned repository separately
and provide its absolute path:

    python3 tools/census.py --repository /path/to/ProveIt --output census-rerun

The static census measures source without executing it. Its eligibility
classification and contract-specific minima require the explicitly
documented manual source review; it is not a proof that every corpus
checker is sound.

BYTE-PROFILE EXAMPLE
--------------------
The new root record combines a goal and initial scope with its first packet.
The following proves I(0,0;u.0)=0:

    printf '%s\n' '[[[[0,0,0],0],0,[],0,0,0]]' | python3 code/checkers/checker.py

Expected output is ACCEPT. For existing four-field certificates, use:

    python3 code/checkers/translate.py < old.json > new.json

For the inverse translation:

    python3 code/checkers/translate.py --backward < new.json > old.json

The stream translator also reads stdin and writes stdout. Its default is
JSON Lines to a reversed whole-JSON array; --to-lines reverses that map.
The translators are untrusted conveniences and are not imported by any checker.

ATTRIBUTION
-----------
The controls, fixtures and mathematical reference material come from the
named ProveIt corpus under its MIT-0 license, included in this archive.
reference/shared_leaf_upstream_provenance.json is the earlier package's
original provenance, not a claim that its older contributions are new here.

The current report deliberately distinguishes inherited mathematics,
new implementation arguments, executed checks and unresolved goals.
