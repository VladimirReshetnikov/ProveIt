# Odd affine root sums for Diophantine consistency

Six literal, division-free integer-coefficient polynomials are supplied.
Every quantified coordinate is unrestricted over the integers.

| Equation | Variables | Exact degree | Live binary operations |
|---|---:|---:|---:|
| `integer16_odd_degree112` | 16 | 112 | 120 |
| `integer15_odd_degree310` | 15 | 310 | 137 |
| `integer15_odd_degree306` | 15 | 306 | 140 |
| `integer16_mod4_degree112` | 16 | 112 | 119 |
| `integer15_mod4_degree310` | 15 | 310 | 136 |
| `integer15_mod4_degree306` | 15 | 306 | 139 |

The sixteen-variable point improves both degree and arithmetic count against
the inspected source16/184/135 and source16/192/134 forms. The fifteen-variable
points are a further variable/degree/cost tradeoff, not a claim of a
world record or a global minimum. Nine-positive and ten-unrestricted-variable
equations in the repository remain separate, much-higher-degree options.

The innovation is to encode several roots by an **odd affine sum**. Rational
square-root integrality then recovers an odd strong-Pell multiplier after its
coordinate has been eliminated. With three roots, parity excludes partial
irrational cancellation; an already available separated-root inequality
excludes the only remaining pair. See `PROOF.md` for the complete argument.

`MOD4_PROOF.md` gives the final refinement: a root sum congruent to two
modulo four uses the already available residue of the first Pell root to
save one gate in each construction. The odd-sum reference equations remain
unchanged. The modulus-four versions are the shorter supplied evaluators.

`equations/` contains the ordered register expressions, complete fully inlined
residuals, variable lists, and single-polynomial finalizers. `circuits/`
contains every binary gate. Registers are abbreviations, not extra variables.
The authentic six coefficient byte strings and finite recipe are in
`coefficients/`. Their 615,883 raw bytes, domains and shifted MF convention
are preserved. No coefficient is left as an unspecified program index.

Rebuild and check using Python 3.10 or later, with no extra dependencies:

```
python3 build.py
python3 check.py
python3 -O check.py
```

The checker does not import the builder. It verifies literal circuit identity,
all live coordinates, fixed coefficient bytes, local norm identities, complete
generic and centered weighted expansions, and nonzero actual-coefficient
degree witnesses. The centered expansion takes several seconds. It does not
search for a ZFC refutation or run a proof assistant.

The ordinary proof establishes exact existence equivalence to the retained
parent, whose full native/Pell/refutation calibration is inherited. Thus its
composition targets a biconditional provable in ZFC. Neither consistency nor
independent unsolvability is claimed. No new end-to-end Lean/Rocq certificate
or object-language ZFC derivation is supplied.

`upstream_builder.py` and `polynomial.py` are retained source tools, with
inherited notices in `licenses/`. The former is used only as a deterministic
arithmetic-DAG emitter; its main routine is not run. The exact parent is
`upstream17.json`, and its ordinary proof is `UPSTREAM_PROOF.md`.

This research and its internal independent reviews were AI-assisted.
Independent AI review is not external human peer review.
