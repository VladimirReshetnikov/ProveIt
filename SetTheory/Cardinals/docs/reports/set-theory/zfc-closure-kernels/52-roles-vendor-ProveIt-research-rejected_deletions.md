# A countermodel to deleting transitivity from exact-fiber hulls

New research, 16 October 2026. This is an ordinary mathematical proof,
independently reviewed; it is not a proof-assistant certificate. Source 03's
delivered EFH theorem retains transitivity. The result below rejects a
further deletion rather than changing the intake's account of that theorem.

Let `EFH−T` be the schema

\[
 [\forall x\exists b\forall y(\varphi(x,y;\bar p)\to y\subseteq b)]
 \to\forall a\exists v\,[a\in v\land
 \forall x\in v\,\exists b\in v\,\forall y
 (y\in b\leftrightarrow\varphi(x,y;\bar p))].
\]

The ambient quantifiers and matrix are unrestricted. Only the requirement
that every member of `v` be a subset of `v` has been removed from EFH.
Keep Extensionality and all matrix instances with arbitrary finite parameters.

**Proposition.** ZFC proves that the set structure `V_{ω₁}` models
`Extensionality + EFH−T`. Consequently ZFC proves this weakened theory's
syntactic consistency.

Work in ZFC and put `M=V_{ω₁}`. This transitive set satisfies Extensionality.
Fix a matrix interpreted in `M`, parameters in `M`, and the schema's local
subset-boundedness premise in `M`. At each input `x∈M` choose, locally,
a bound `b∈M`. Every output is an actual subset of `b`, because `M` is
transitive. Separation in the actual `P(b)` gives its exact fiber

\[
 F(x)=\{y\in M:M\models\varphi(x,y;\bar p)\}.
\]

It belongs to `M`: it is a subset of `P(b)`, so its rank is at most
`rank(b)+1`, which is still below `ω₁`. The exact fiber is independent
of the bound; Extensionality gives uniqueness. No uniform choice of
local bounds is needed to define `F`.

For each seed `a∈M`, ordinary recursion in ZFC constructs the sequence
`a,F(a),F²(a),…`. Let

\[
 v=\{F^n(a):n\in\omega\}.
\]

Countably many countable ranks have countable supremum. Thus `v∈M`;
it contains `a`, and if `x∈v`, then `F(x)∈v`. This is the required
exact-fiber witness. Repetitions in the orbit are harmless.

Satisfaction for the set structure `M` makes the argument uniform over
coded formulas and finite parameter assignments, so it supplies the model
for the entire recursively axiomatized schema, not just finitely many
handpicked matrices. The ordinary soundness argument yields consistency.

If ZFC is consistent, this excludes a ZFC proof that this weakened theory
is equiconsistent with ZFC: combining that equivalence with the consistency
proof above would give ZFC a proof of its own consistency. The argument
is specific to this deletion. It does not assert that every theory lacking
a displayed transitivity conjunct has the same strength.

The reason the countermodel does not satisfy full EFH is also concrete:
the orbit set is closed under the function `F`, but it need not contain
the members of its own elements. Source 03's transitivity requirement adds
exactly that further closure, which its ZF-strength bootstrap uses.
