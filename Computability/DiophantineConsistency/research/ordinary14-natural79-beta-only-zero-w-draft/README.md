# Natural-79 zero-w exclusion with represented beta alone

This source-only alternative strengthens the proposed zero-`w` theorem: in any model with the assumptions of the existing model lemmas, if the 79 graph has a zero and its beta port is the embedding of a model-natural `beta`, then the witness's `w` coordinate is positive. `beta` and `J` may be zero; the other three integer ports need no natural representation, positivity, or bounds for **this 79 step**. The four inert `.lean.src` snapshots adapt the signed-main-norm, root-cut, slim divisibility client and endpoint sources. None has been parsed or elaborated by Lean, and the older sources and receipts remain intact.

The mathematical observation is independent of a stronger positive-J argument. Set

```text
q = 1 + J*beta,  Y = q³*(n_s+1),  U = Y*q²,  H = 4Y+3.
```

In a natural model `q ≥ 1`, `Y ≥ q³` and `U > 0`, even if beta or J is zero. At `w=0`, the existing first-factor and residue arguments propose that all five factors of a zero are positive units. The main unit gives a signed root `D` with `D² = U²(1+(Y²+H)c²)`. The existing signed-magnitude and positive-scale quotient lemmas supply a signed `d` with `D=U*d` and `d²=1+(Y²+H)c²`, retaining both signs.

The exact zero-`w` root cut gives `U(d−Yc)=H*z` for some difference-ring `z`. Multiplying by `d+Yc` and using the norm gives the explicit ring identity

```text
U = H * (z*(d+Yc) - U*c²).
```

Writing `U=H*t` and using `U=Yq²` yields

```text
3q² = H * (q² - 4t).
```

The existing corrected reflection helper proposes converting this signed divisibility to the natural-model statement `H ∣ 3q²`. But `0 < 3q²` and, since `q³ ≥ q²` and `Y ≥ q³`,

```text
3q² < 4q²+3 ≤ 4Y+3 = H.
```

A positive multiple of `H` cannot be strictly smaller than `H`. This is a contradiction, so a zero cannot have `w=0`. For the boundary `beta=0` or `J=0`, `q=1` and the same strict inequality remains valid. The ring identities require no cancellation, choice of the root's sign, or factorization into standard primes. This argument still depends on the full model assumptions, the first/main factor and residue lemmas, the model quotient, the signed-to-natural reflection, and their eventual Lean verification.

The alternative main-norm snapshot copies `eval_one_of_pair_unit` verbatim from `Natural79ZeroWJPos.lean` with attribution, then drops its import of that J-positive source. It removes the unused beta/J positivity arguments from `scale_pos` and the quotient. The root snapshot propagates that weaker interface. The divisibility snapshot starts from the corrected slim-client alternative and replaces `q≥2` with `q≥1`, removing its J-positive dependency and K0/beta-positivity premises. The endpoint snapshot applies the weaker theorem at the existing compact beta representation. It deliberately retains the earlier endpoint imports; in particular, the separate 80 endpoint and strict-K0 obligations are **not** removed by this observation. No graph, operation count, displayed Carrier65 equation, or user-visible PDF is changed.

The checker pins the original draft sources and candidate graph, reconstructs each replacement exactly, checks that its snapshots match, and symbolically checks `q`, `Y`, `U` and a ring identity behind the `q≥1` size comparison. It does not check Lean syntax, elaboration, namespace resolution, theorem imports, tactic execution, complete providers, or axioms. The snapshots have the same module and namespace names as the originals, so they are alternatives, not modules to import simultaneously; materialization needs a separately reviewed source selection and collision/provider plan.

An [independent source and mathematical review](../../reviews/ordinary14-natural79-beta-only-zero-w-independent/README.md)
checks the source deltas and the `q=1` boundary without elaborating Lean.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural79-beta-only-zero-w-draft/check_source.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural79-beta-only-zero-w-draft/receipt.json
```
