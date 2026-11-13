# Exact-binding threshold checker: claim and proof notes

Candidate: `exact_threshold.py`.
Measured normalized source: **314 tokens, 357 AST nodes, 590 UTF-8 bytes**.
Matched intrinsic-validation control: **316, 360, 591**.
Inspected exact-canonical incoming envelope, by different source files: **316, 358, 591**.
The candidate is strictly below each coordinate of that exact-public-grammar envelope.
It is not below the compact promised-grammar envelope and makes no mathematical-minimality claim.

## Public interface is unchanged

The source code's opener `i` is byte-for-byte the intrinsic-validation control's opener. Its public call still occurs with `k=0`, default formula depth `d=0`, and unusable default image `t=c`. Hence it accepts exactly the canonical Eq/D formulas with genuine bound-variable positions. In a numerical position code 1 is zero (JSON true is a permitted equal alias), code `3+2j` is bound numerical slot j, singleton lists are successor, and ternary lists are iterator; only the iterator's third child binds a new variable. A singleton formula binds two variables, and a pair is equality. Negative scalar parameter names cannot occur in the public closed goal.

The whole document is parsed by the standard JSON reader. The final list element is the goal; preceding packets are consumed by pop. Acceptance remains normal termination with the exact line `ACCEPT`. No certificate code executes; no external proof function or rule table is imported. Finite resource exhaustion rejects in a real process; the completeness claim uses the same unbounded finite-run mathematical idealization as the repository.

## Changes

1. `from json import load; q=load(open(0)).pop; c([[]],q())` becomes `import json; c([[]],(q:=json.load(open(0)).pop)())`. Evaluation still obtains and assigns the same bound pop method before invoking c. No proof operation moves across a reader operation.
2. The elimination goal selector becomes lazy. Instead of constructing both `(a, i(t,s))` before testing `(m,a)==(expected_major,i(t,u))`, it uses `i(t,s) if condition else a`. This removes a traversal of a source that is discarded when the elimination test fails.
3. The introduction mode test changes from `len(a)==2==u` to `len(a)==2>u`. The new convention is progress when the matrix is an equation and the control field u is less than 2; otherwise the introduction is by cases. The canonical compiler uses u=0 for progress and u=2 for case introduction at an equation. For a compound matrix the comparison short-circuits after `len(a)==2` and the rule is always case introduction.

## Soundness of the lazy source

In a successful nonterminal call, the major subproof is checked before either version forms the continuation's goal. There are two cases.

* If the elimination test is true, the candidate evaluates both `i(t,u)` and `i(t,s)` at the same unchanged floor as the control. `i` is pure apart from reading the global floor. Reordering these terminating traversals does not alter their results. The checked major and its two checked instances justify the same equality or closure elimination.
* If the test is false, the continuation's goal is the current a, regardless of s. The source does not enter the retained context (which is built from m or the introduced matrix), the instantiated successor goal, or any assumption. Its previous traversal was an unused rejection check. The continuation is justified by the same D-opening or introduction inference. The target traversal `i(t,u)` remains evaluated; no proof of an inferred major is skipped.

The source may still affect the terminal computation candidate or the failed elimination comparison. In a terminal computation match, the code is unchanged and the original soundness argument applies. In a failed comparison it contributes no premise. The claim is therefore inference-level soundness, not equality of the two raw accepted byte languages.

## Soundness of threshold mode selection

The calculus permits DI by cases for an arbitrary matrix and DI by progress only for a literal equation. The chained comparison `len(a)==2>u` can be true only when a has exactly two children. Thus every newly selected progress instance is still an allowed equation-induction instance. Every false comparison selects the already allowed case rule. A noncomparable u raises an exception when the comparison reaches it and so cannot create an accepting run. No property of the numerical value u is asserted as an arithmetic theorem: it is a proof-mode control field.

## Completeness and certificate translation

Use the inherited canonical compiler for the same scalar Choice-DI rules. At each actual introduction whose instantiated matrix is an equation, replace the old mode field 2 by 0 (progress), and replace the old non-2 case field by 2. Other packet fields, the theorem code, all numerical terms, every de Bruijn coordinate, and all negative parameter names remain unchanged. Compound introductions need no mode change.

Why the changed control field is harmless outside mode selection:

* At entry to an introduction the goal is unary D, while the computation candidate is an equality pair, so changing u cannot turn that call into an accidental computation leaf.
* The introduction's major is the inert empty-list token. Its expected elimination major is a nonempty pair or triple, so the elimination test is false regardless of the target-instance check.
* The auxiliary target traversal on a canonical witness terminates for either control value 0 or 2: if it exposes an image, `i(0,d=3)` and `i(2,d=3)` both terminate. This traversal contributes no resulting formula in the introduction case.
* The base/step assumption and the successor continuation are determined by the actual matrix and the selected mode, which are preserved by the translation.

Induction on the canonical proof tree therefore gives an accepted candidate certificate for every theorem produced by the inherited compiler. The converse follows from the soundness cases above and the unchanged underlying rule calculus.

`translate_threshold.py` is an untrusted trace-based producer for the supplied old four-field fixtures. It records actual introduction calls under the original checker and changes only their mode fields. `threshold_fixtures/cases.json` gives the exact changed packet indices. Fourteen inherited certificates pass, including equation induction with a used hypothesis, compound implication elimination, numerical zero symmetry, and derived zero-source transport. Finite tests supplement, rather than replace, the preceding proof.

## Mathematical and novelty boundary

This is a new composition of intrinsic exact-binder validation, lazy elimination-source validation, and a threshold convention for the existing mode bit. It deletes no arithmetic or logical axiom. The ordinary realization is exactly the repository's scalar Choice-DI realization; its iPRA bi-interpretation and identity numerical comparison maps are inherited. The contribution is a measured complete-checker refinement in one explicitly identified interface class.

Do not claim that a best observed source size is a proved lower bound, that 314/357/590 is globally minimal, or that this meets the user's stronger target of beating all compact checkers. It does not.
