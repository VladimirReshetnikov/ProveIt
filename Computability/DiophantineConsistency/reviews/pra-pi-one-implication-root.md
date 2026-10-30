# One-induction transfer for unary Π₁ equivalences

`PRAPiOneImplication.eliminate_one_from_equivalence` gives an actual candidate-PRA
proof of `(∀x p(x)) ↔ (∀x q(x))` from an actual proof in candidate PRA plus
one closed induction instance for `∃y ψ(x,y,c)`, provided `p`, `q`, and `ψ`
are open formulas of the stated arities. It translates each implication into
`∀y ∃x (¬p(x) ∨ q(y))`, invokes the previously established one-instance
elimination, and reconstructs the equivalence. Completeness and classical
reasoning are used in Lean's metatheory to construct classical object-theory
proofs; no standard-model-to-provability inference occurs.

This is **not** the PRA consistency-equation endpoint. The actual no-zero
and consistency sentences still need to be put into the unary open-matrix form,
including verified tuple coding and bounded-formula handling. Arbitrary finite
induction instances and the comparison with a standard PRA presentation remain
open. The endpoint uses one closed induction instance, with its single
induction parameter and no additional external predicate parameters.

The author and independent isolated builds used, respectively,
`/tmp/pra-after-preparation-merge-refresh-o2iil0it/lib` and the independently
replayed `/tmp/pra-after-preparation-merge-independent-y_kpfny8/lib` as their
parent providers. Main and check modules both succeeded without warnings;
source, object and complete log hashes agree:

| Module | Source SHA-256 | Object SHA-256 | Log SHA-256 |
| --- | --- | --- | --- |
| `PRAPiOneImplication` | `95b6520c11e3428454e7a888085638967c16b996d290c3e3656d1d837dead8fb` | `d4b549181f83d2f1e02296a07b82156b5df9c5900282837f3f3d036482d73206` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `PRAPiOneImplicationChecks` | `44ef214600567820f44a22b78bee1d7e8021d4e0118481bfba786824cb0bbc14` | `f2efcda978f46b8d025bf602bcd5c33950971316ada66ecdc1a472b6d217d96f` | `23be28d386f6e9a46ff9ed8d7f20ecaafb7e29e9ab0b7519807145ff15a71bf6` |

The four axiom reports in the retained [logs](pra-pi-one-implication-replay/)
show only `propext`, `Classical.choice` and `Quot.sound`, as applicable.
The independent source reviewer checked the model equivalence, nonempty-domain
requirement, open-matrix hypotheses, closed induction instance and separation
between metatheory and object theory. The parent provider is separately scoped
by the 47-module post-preparation-merge replay; Foundation and Mathlib are
inherited boundaries, not freshly rebuilt by this client. An earlier author
attempt failed because the isolated output directory did not contain the
inherited module tree; it created no accepted object and was replaced by a
fresh symlinked-provider build.
