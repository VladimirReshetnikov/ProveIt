DIRECT ONE-SORTED EQUATIONAL BACKEND
18 October 2026

This is an independent complete frontend/search route for the small ZFC
consistency-machine project. It is not a binary Turing-machine table or a
claim to have crossed 245 states.

MAIN RESULT

For every finite equality-free universal clause theory T with a constant,
the supplied algebraization yields equations E(T) such that, in ZFC:

  T has a model
    iff E(T) has a nontrivial Boolean model
    iff no ground rewrite zigzag joins N(top,top) to top.

The model proof is one-sorted and does not assume the original functions
preserve Boolean operations. The reverse construction keeps the entire
Boolean carrier and applies an ultrafilter only to predicate values.
Ground-rewrite completeness is proved with a term-algebra quotient.

CONCRETE INPUT AND OUTPUT

Input: existing FC13B equality completion, 23 clauses, 57 literals,
1,499 bits in the inherited clause-payload format. No equality clauses
have been silently removed. Eq is reified as a predicate before applying
the theorem.

Output: 21 equations, 42 rewrite orientations, 446 expanded term nodes.
The complete new packet costs 2,324 bits: 2,252 equation bits, 52 header
bits, and 20 endpoint bits. The new data are larger; any future machine
saving must come from compiling the simpler ground rewrite engine.

The Boolean basis is the known 15-symbol single Sheffer law Sh1 of
McCune et al., Short Single Axioms for Boolean Algebra, JAR 29 (2002),
Theorem 2. Primary paper and original proof files:
https://www.cs.unm.edu/~mccune/papers/basax/
https://www.cs.unm.edu/~mccune/papers/basax/v12.pdf

REPRODUCE

Requires Python 3.10 or later, standard library only. Run in this folder:

  python verify_backend.py
  python equational_search.py demo_theory.json --search-below 184
  python equational_search.py demo_theory.json --proof demo_proof.json

The artificial inconsistent test first halts at proof code 183, after
checking 184 candidates. Its actual two-step proof is 0 -> p(d,d) -> 1.
It is not a proof about FC13B or ZFC. The optional unbounded search is
obtained by omitting --search-below; no time limit is silently imposed.

FILES

equational_reduction.tex: Full ordinary mathematical proof and report section.
equational_search.py: Ground rewrite verifier, bijective natural codecs,
  and fair exhaustive enumerator.
build_equations.py: Exact input translation, checked Boolean regrouping,
  bounded NAND synthesis, and full packet serializer/parser.
verify_backend.py: Semantic, certificate and numeric-interface checks.
grouped.json, grouped.bits, grouped.equations: Recommended complete target.
literal.*: Literal clause conversion control with 8,983 complete packet bits.
metrics.json, verification.json: Exact reproducible results.
demo_theory.json, demo_proof.json, demo_trace.json: Artificial contradiction.
reference/FC13B_complete.json: Frozen prior input.
reference/input_manifest.json: Archive identity, source hashes and input size.

BOUNDARIES

No new formal proof-assistant build, complete RM/TM compiler, binary state
count, global encoding optimality or nonhalting proof is claimed.
The Sh1 basis theorem is cited from its primary proof. Finite checks of
that law are regressions and do not independently prove its sufficiency.
The class-theory calibration is inherited, not claimed as a new result.
The new theorem and checker are useful irrespective of whether another
source-theory compression later supplies a shorter clause input.
