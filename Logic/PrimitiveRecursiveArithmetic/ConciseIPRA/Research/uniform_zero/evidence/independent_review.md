# Final skeptical review

This is a separate model review performed within this research task, not an
external human peer review or a proof-assistant verification. It examined the
mathematical arguments, the constructed-major implementation, and the final
report.tex and new_theory.tex. The delivered program hashes and finite test
results are in evidence/metrics.json and evidence/validation.json.

## Outcome

The review found no new soundness contradiction, bi-interpretability
obstruction, or mismatch between the selected checker and its claimed rules.
It identified one expository omission in the final report: the gate and
formula-selector recursions were displayed for equation/D formulas even
though the public grammar also includes Q. The report now explicitly expands
every Q_y B to D_(w,y) B with w fresh and unused before applying those
recursions. The already stated unused-witness equivalence justifies this.

The axiomatic basis remains inherited. The report correctly separates the
545-byte implementation control from the 550- and 556-byte new presentations.
The review does not establish an absolute minimum or the requested new
foundational breakthrough.

## Uniform zero and opening

The selected new profiles use `a or 1` for a preserved scalar. At a meaningful
numerical root, depth is at least three and coordinates 0, 1, 2 denote zero.
Only a preserved falsy scalar changes: integer or floating zero, signed zero,
or Boolean false. Replacing it by 1 therefore preserves the interpretation.
Protected state coordinates start at three; admitted negative rigid names
are also truthy. At scalar formula positions the values denote truth padding.
Changes below constant-meaning surplus nodes affect ignored annotations.

The exact syntactic commuting theorem is properly restricted to the stated
canonical codec. Instruction markers are not recoded. Arbitrary accepted
aliases need the semantic opening lemma; arbitrary raw-tree idempotence is
not asserted. The recoding moves no binder and removes no protected slot.

## Constructed majors

There are three cases in the truthy-mode branch:

1. A truthy source constructs `[s,u]`. The checker proves that exact equation
   before replacing a matched target instance by its source instance.
2. A falsy source and truthy template construct `[t,t,t]`. A successfully used
   falsy numerical source denotes zero, giving the ordinary Q rule. An
   irrelevant unused image need not be validated as a numerical expression.
3. Falsy source and template retain the supplied major. A unary major gives
   the existing paired-elimination rule. Any successful target match through
   a falsy formula template concerns truth padding, so it supplies no new
   nontrivial conversion rule.

The recursive proof of a constructed major is essential. Construction from
untrusted fields is not acceptance of those fields as a theorem. The mutation
tests demonstrate that omitting this proof admits a false equation.

## Scopes, generated assumptions, and dispatch

Every delivered profile uses a local floor. A major premise receives the
current floor, but allocations within its completed proof do not alter the
parent floor. Name reuse across disjoint scopes is alpha-renaming. The
supplied local producers restore their floor after emitting a major proof.
Compatibility with a global-floor producer is not assumed.

No checker mutates the default context list; extensions use concatenation.
The shared Boolean hypothesis selection is sound because a successful
nonempty major has a nonempty export and a computation constructs a nonempty
pair. Unsupported null arithmetic markers reject; canonical packets use 0.

A generated computation assumption H(b) need not be uniformly true. Its
provable zero instance H(0), followed by substitution in a continuation whose
retained context and goal omit b, is the needed invariant. For accepted
fractional names, all additional fresh names used in the new unit interval
are specialized separately to zero. They are not silently identified with
the designated integer eigenparameter.

## Quantitative statements

The N+2r versus N node theorem concerns the explicitly specified old
three-node repair of r excluded computation leaves. It is not a lower bound
on all old proofs or on shortest serialized certificates. Hypothesis closure
can suppress packets, and altered name allocation can change decimal widths.

With the encoding and labels fixed, replacing an explicit equality major by
a one-byte flag saves exactly |s|+|u|+2 compact JSON bytes. Replacing a
triplicated Q major saves exactly 3|B|+3. The latter removes duplication in
the packet and does not remove the codec's independent duplication within
nested formula representations.

The final package's 504 acceptance/rejection expectations and four guard
mutation checks are finite integration evidence. The 16-example certificate
totals are sample measurements, not a universal compression ratio. The
mathematical universal claims remain supported by the written proofs and
the explicitly attributed inherited bridge, rather than by testing alone.
