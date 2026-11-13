NEWEST SPECIALIZATION WITH INFERRED EXPORT
========================================

New contribution
----------------
The normalized deterministic-export calculus can restrict all ordinary
clause applications to the newest free numerical parameter (or 0 in an
empty scope), with no supplied specialization term. Arbitrary reflexivity
and arbitrary introduction witnesses remain available. The exact
all-open-sequent equivalence theorem is in theory.tex, including the
necessary stronger induction over injective renamings and context
extensions. It derives the restriction without a primitive Alias rule.

Prior-art boundary
------------------
The repository already proves newest-only clause use with a primitive
fresh-alias rule (alias_back / equation_aliases), and already has the
deterministic-export calculus (clause_discharge / XCPrf). The new theorem
combines these reductions by constructing names with Intro and replacing
the alias discharge by the existing deterministic Export. It does not
claim that naming or newest-parameter specialization is a new idea.

Checkers and metrics (CPython 3.12.14)
------------------------------------
checkers/reference_clause.py: 653 tokens / 729 AST / 2058 normalized bytes.
  Exact pinned upstream clause_discharge checker, with a fixed reflexivity
  clause and arbitrary specialization targets supplied in each Use packet.

checkers/newest_reflexive_clause.py: 654 tokens / 731 AST / 2049 bytes.
  Complete compact candidate. Nine bytes are saved against the pinned
  control, at a cost of one token and two AST nodes. A Use packet has no target field.
  Context index 0 remains the unrestricted reflexivity scheme, whose
  instantiation term is inferred from the validated goal's left side.
  All other Use packets specialize at the newest parameter.

checkers/reference.py: 669 tokens / 754 AST / 2117 bytes.
checkers/newest.py: 663 tokens / 748 AST / 2093 bytes.
  Clean matched pair with primitive Refl, isolating the mathematical Use
  restriction from the additional inference of a reflexivity target. The
  clean matched pair improves all three coordinates; the compact pair
  improves bytes only.

All complete programs include JSON input, scope and syntax validation,
full normalization, substitution, every inference rule, and the verdict.
No external helper is imported by the checkers. No eval or exec is used
in them. Acceptance is zero exit status and the exact line ACCEPT.
An exception rejects. Physical resource exhaustion is not acceptance.
The theorem-level proof relation is the finite-derivation relation.

This does not beat the entire current checker envelope. It is a smaller
matched implementation of a newly restricted logical interface.

Reproduce
---------
  python3 -B verify.py

This compiles nine pinned upstream certificates to the primitive-Refl
reference, to the newest-use calculus, back to the reference, and to the
compact reflexivity-clause protocol. Complete checkers are also run as
isolated subprocesses. Open-context and renaming/capture tests exercise
the stronger theorem; negative controls test typing, fresh scope,
malformed targets and false goals. Results are in verification.json.
translate.py is an untrusted proof producer, not a checker dependency.

An individual complete theorem certificate can be replayed using:
  python3 -I -S -B checkers/newest_reflexive_clause.py \
    < tests/compact_successor_congruence.json

The command-line endpoint accepts [closed_goal,proof], not external open
contexts. Internal open-context tests use well-scoped compatible encodings;
the mathematical theorem is stated for independent arbitrary scopes and
clause contexts. Each eigenparameter introduction adds a context entry,
so the closed proof format recovers its fresh scope from context length.

Provenance
----------
Repository: VladimirReshetnikov/ProveIt
Pinned commit: 2fa4637b3bf922beea0052a5210c22b14482950b
Root: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
Control: Artifacts/clause_discharge/code/checker_deterministic.py
Source fixtures: Artifacts/clause_discharge/validation/examples/*.json

The source control and nine source certificates are reproduced under the
repository's MIT-0 license. Code adaptation, the newer restrictions and
proof translations are explicit in this package. The mathematical bridge
and normalization results are inherited from the pinned consolidated
article (Chapters 1, 4 and 6); no new Lean elaboration is claimed.

Further questions
-----------------
1. Can the same target deletion lower the best compact checker rather
   than just this fully normalized clause-discharge implementation?
2. Can arbitrary Refl be recovered after also restricting the fixed
   reflexivity clause? The current name construction needs Refl at t.
3. Can Intro witnesses and Use targets both be restricted without a
   circular naming argument?
4. Does the raw five-family companion in theory.tex yield a better
   matched complete checker? Its equivalence is proved in writing, but
   no raw implementation is included in the size claims above.
