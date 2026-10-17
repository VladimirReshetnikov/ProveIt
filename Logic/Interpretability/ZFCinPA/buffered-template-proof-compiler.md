# Proof templates with a finite variable-shift buffer

The [compiler](Lean/ZFCinPA/BufferedTemplateProofCompiler.lean) translates a
fixed ordinary proof into an actual represented internal proof. Its translation
is indexed by an ordinary natural-number buffer. The formula codes inserted
by that translation may be arbitrary internal elements with free parameters.

Universal introduction compiles its child with one additional shift. An
explicit source SHIFT compiles its child with one fewer shift, then emits the
actual internal SHIFT rule. A finite bound computed from the source proof tree
counts SHIFT nodes along each branch; starting with that bound prevents
underflow. Other rules keep the buffer. Source axioms are supplied by actual
target proof callbacks at each buffer, allowing proved open schema instances.

For a closed source conclusion, the translation laws identify the buffered
conclusion with a finite shift of the desired translation. The checked
[shift-cancellation construction](model-coded-shift-cancellation.md) removes
that buffer. The resulting target formula can still have free parameters.
No inverse map on internal free-variable labels is assumed.

`BufferedTranslation` states the required constructor, substitution, and
cross-buffer shift/free equations explicitly. This checkpoint proves the
logical compiler under that interface. A concrete predicate translation,
its axiom callbacks, and Collection remain separate obligations. Recursion is
over the fixed external proof tree, not arbitrary internal proof codes.

The 256-line source and [audit](Lean/ZFCinPA/BufferedTemplateProofCompilerAudit.lean)
pass seven axiom probes and nine callers with standard Lean axioms only and
zero warnings. Source/audit times are 6.071s/2.312s. The
[successful record](results/buffered-template-proof-compiler-verification.json)
checks all 50 inputs, twelve project predecessors, seven direct external
boundaries, the actual first Init/Omega providers, and the fresh object.
ShiftCancellation is actually imported. Coding is an additional pinned direct
external boundary; the existing Foundation namespace is reused without a full
rebuild. No dependency build or download occurred.

Three unsuccessful source attempts are preserved in the
[history](results/buffered-template-proof-compiler-history.json). Repairs fixed
recursive section-argument elaboration, singleton membership simplification,
and the way Lean constructs the dependent recursion. The final implementation
uses explicit induction over the same proof tree with the buffer generalized;
its statements and proof-rule cases are unchanged. No resource option was raised.

```bash
python Logic/Interpretability/ZFCinPA/check_buffered_template_proof_compiler.py --output /tmp/buffered-compiler-replay
```

The runner accepts explicit repository, dependency, source/audit, parent,
cache, namespace, compiler, and library paths. Its maintained copy is identical
to the executed guard. Packaging adds an unbuilt default preparation and
[independent review](results/buffered-template-proof-compiler-review.json),
with no successful-proof replay or additional rejection controls.
