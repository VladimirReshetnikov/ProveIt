# 76-operation independent-`y` candidate

Starting with the 77-operation unit-product graph, replace the positive input
`e` by an independent positive input `y` and remove the gate `y=V+e`. All
other 76 gate rows and the other 13 witness coordinates are unchanged. The
new graph has 14 positive witnesses and 76 live operations: 42
multiplications, 18 additions and 16 subtractions.

The graph expressions agree algebraically under `y=V+e`. The positive witness
maps use zero-specific facts: `V+e` need not be positive for an arbitrary
parent tuple, and `e=y−V` is positive only when `y>V`. Since the graph uses
`y` only through `y²`, the forward map chooses `|V+e|` after proving it is
nonzero. A separate
[mathematical analysis](../p64-qcube76-independent-y-analysis/README.md)
examines the required zero-specific inequalities, with an independent
[argument review](../../reviews/p64-qcube76-independent-y-math-independent/README.md).
The generic [inequality lemmas](../p64-qcube76-independent-y-lemmas-draft/README.md)
and [ring bindings](../fourteen-p64-qcube76-independent-y-binding-draft/README.md)
now check in Lean. A guarded [model split and main-root check](../p64-qcube76y-graph-model-guarded-check/README.md)
also passes, as does the [actual-zero size bound](../p64-qcube76y-size-guarded-check/README.md)
`f²>c+1`. Both the new→old [strict-root guard](../p64-qcube76y-strict-guarded-check/README.md)
and old→new [nonzero-root guard](../p64-qcube76y-oldroot-guarded-check/README.md)
also pass. The [witness maps](../p64-qcube76y-witness-guarded-check/README.md)
and [full positive-zero join](../p64-qcube76y-join-guarded-check/README.md)
now check for arbitrary natural ports in the stated IΣ₁ models. The guarded
[iPRA client](../p64-qcube76y-ipra-guarded-check/README.md) also checks the
native, standard and equality-only derivability statements for the symbolic
Lean graph and selected mapped Foundation refutation negation. No
full graph-zero counterexample is claimed. The maintained root `equation.tex`
and `equation.pdf` are unchanged.

The [full model join](../p64-qcube76-independent-y-full-join-draft/README.md)
and [iPRA client](../p64-qcube76-independent-y-ipra-draft/README.md) have
passed guarded checks against captured providers. Complete transitive
provider ancestry and external payload/display identification remain separate.

[`build.py`](build.py) checks the auxiliary identity under `y=V+e` in an exact
polynomial ring, verifies the 76 unchanged parent rows and all input/gate
liveness, reruns four pinned P64 residual identities, and compares all five
residuals and the output on 600 deterministic modular substitutions. These
modular substitutions are algebraic checks; the lifted `y` is not asserted
to be positive.

The same builder computes exact leading forms: residual degrees are 22, 34,
22, 30, and 2, and the output has degree 104 for `beta != 0`. Its leading
homogeneous form is

```
beta^56 * J^56 * T^4 * f^12 * s^16 * w^8 * (eta+zeta)^8.
```

The increased degree relative to the 77 graph comes from losing the
cancellation caused by `y=V+e` in the auxiliary residual. As an independent
sanity check, [`check_ray.py`](check_ray.py) fully evaluates the graph as a
univariate polynomial over a finite field: its specified ray has degree 104
and leading coefficient 640860 modulo 1000003, matching the expression
above. This single ray does not prove the general upper degree. The complete
results are [`checks.json`](checks.json), [`ray-check.json`](ray-check.json),
and [`external-check.json`](external-check.json).

[`generate_lean.py`](generate_lean.py) transcribes the graph to
[`P64QCube76Y.lean`](P64QCube76Y.lean), which passed a bounded
[guarded Lean compilation](../p64-qcube76-independent-y-guarded-check/README.md)
against captured providers. That check verifies the definition elaborates;
it does not rebuild its complete provider ancestry. The external evidence
does not prove zero equivalence, Lean/JSON or PDF
semantics, or global minimality. To reproduce it:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/p64-qcube76-independent-y-candidate/build.py
python3 -I -S -B Computability/DiophantineConsistency/research/p64-qcube76-independent-y-candidate/generate_lean.py
python3 -I -S -B Computability/DiophantineConsistency/research/p64-qcube76-independent-y-candidate/check_ray.py
```

| Artifact | SHA-256 |
| --- | --- |
| `build.py` | `c3948cfdb14080e0fdb0e5d0c7796fa808a216bfb5a8442041c23284cde422b4` |
| `graph.json` | `196ef3bdf6805c7ed7d44c278359e32c0f658634db357cc19f0e87464ed6b11c` |
| `checks.json` | `e221862166447f7224af1d9ebc2e53f8d9cc036efdc46c6a19196eeb74b58b33` |
| `generate_lean.py` | `97f815cffbe40d282f75f7bda2d38554a6eb20684e72e4e5b7617708da3330c4` |
| `P64QCube76Y.lean` | `44486d50fa9867c167a111ee6bab23fc3fe7bc17f5ded2b9c1136e643f6de644` |
| `check_ray.py` | `76c135711203f3ba4ef5b23364b7980c88948a74bc36776899d415415dfe2806` |
| `ray-check.json` | `cc890a412c8c65bdbcfebf58f4e4add186efb9b031a742a6587eae20f62f741c` |
| `external-check.json` | `99efadb6640fb6fabf1b369f8e16130ce66330127cb73540249b0254469523bf` |
