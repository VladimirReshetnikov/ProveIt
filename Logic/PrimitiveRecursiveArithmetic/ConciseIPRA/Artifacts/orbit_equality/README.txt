ORBIT EQUALITY AND CONCISE iPRA
Prepared for Vladimir Reshetnikov, November 12, 2026

READ FIRST
  ipra_orbit_equality.pdf
  ipra_orbit_equality.tex (complete standalone LaTeX source)

RESULT AND LIMIT
The main mathematical result is a new use of the existing absorbing orbit:
a 44-node Boolean equality indicator, or a 45-node zero-true equality term.
The latter replaces the article's specifically identified 193-node
subtraction-based equality macro, expanded with its smallest stated P45.
Both inputs occur once instead of three times. This is a derived-term
improvement, not a deletion of a primitive axiom or inference rule.

A generic diagonal-iterator lemma also shortens the proof of the existing
45-node predecessor. It avoids the separate below-cap invariant and a
general comparator-diagonal induction. A 37-node symbolic certificate
verifies the generic lemma using exactly two equation-induction steps.

Two complete whole-JSON checker compositions measure 248/277/615 and
254/268/613 (tokens/AST nodes/normalized UTF-8 bytes). They improve the
inspected whole-JSON token and AST coordinates, respectively, from 249
to 248 and from 269 to 268. They do not improve the existing JSON-lines
243-token/264-node coordinates or the 473-byte coordinate. No one program
attains the whole coordinate envelope. These checkers implement the
inherited guarded calculus; they do not implement a new primitive basis
obtained from the equality macro.

The requested new axiomatization below every current complete-checker
minimum has NOT been established. No absolute minimality, theoretical
lower bound, or new Lean/Rocq formalization is claimed. The paper states
the complete inherited ordinary axiomatization, the new proofs, both
interpretation maps and formula round trips, the guarded native rules,
all input-contract qualifications, and further research questions.

REPRODUCE
  python3 reproduce.py

This verifies all file hashes when MANIFEST.sha256 is present, checks the
exact source metrics, and runs the supplied arithmetic, framing and symbolic
certificate checks in a temporary copy. It preserves the delivered files.
Use CPython 3.12.14 for the quoted exact normalization measurements.
All executable checks use only the Python standard library.

Compile the paper with a standard TeX installation:
  pdflatex -interaction=nonstopmode -halt-on-error ipra_orbit_equality.tex
  pdflatex -interaction=nonstopmode -halt-on-error ipra_orbit_equality.tex

EXAMPLES
  python3 code/equality_orbit.py
  python3 diagonal_certificate/verify_certificate.py
  python3 checkers/whole_json_tokens.py < whole_json_validation/fixtures/literal_zero_successor_repair.json

CONTENTS
  code/equality_orbit.py
      Raw scalar-term builders, exact counters, evaluator and diagnostics.
  evidence/
      Expanded de Bruijn ASTs, receipts, source-search diagnostic and reviews.
  diagonal_certificate/
      Transparent equational verifier, untrusted producer, 37-node proof,
      four negative controls and verification receipt. This is a focused
      symbolic proof checker, not a full standalone iPRA checker.
  checkers/
      Two complete measured whole-JSON acceptance programs.
  whole_json_validation/
      Exact incoming stream controls, candidate copies, both-direction
      transducer, focused genuine proofs/negative controls, and provenance.
  reference/
      Exact pinned article chapters and comparison checkers. The source
      chapter fragments are dependencies for reading, not standalone TeX
      build targets. The 473-byte checker is an unchanged comparison.
  CLAIMS.json, PROVENANCE.json, MANIFEST.sha256
      Precise claim boundaries, repository identities and delivered hashes.
  LICENSE.txt
      Upstream MIT No Attribution license, also applied to this contribution.

BASELINE
Repository: VladimirReshetnikov/ProveIt
Commit: 6c6a164d211f0af34e913d55c9f46f8ef7cb560f
Scope: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA, including all eight
current docs/incoming ZIP archives. No remote repository was modified.

Proof independence means a separate audit during this research task, not
external human peer review. Finite checks supplement the universal written
arguments and do not establish them by exhaustive testing.
