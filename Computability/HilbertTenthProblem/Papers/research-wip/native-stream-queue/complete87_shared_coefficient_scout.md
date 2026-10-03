# A bounded shared-coefficient search inside the complete87 source

No operation saving occurs in this specific multiplication-only family. The actual complete normalized asymmetric source has **87=48M+39A**, degree169, ordinary positive input and19 positive witnesses. Keeping all other arithmetic unchanged, its strong and auxiliary coefficients require at least four new multiplications even when the already-paid main-norm port `Delta*c²` is available. Every smallest schedule still gives87 complete operations.

This is not a lower bound on universal Diophantine circuits. In particular, it does **not** cover the separate direct-first-root coordinate change `T=L+g`, whose five-gate first norm supplies the [proved complete86 construction](complete86_factored_first_root.md). This bounded search was paused to audit that candidate and then frozen independently.

## New family, distinct from the previous scouts

The prior `complete87_joint_norm_scout`, `complete87_discriminant_shear_scout`, `complete87_strong_norm_composition_scout`, and `complete87_new_scout` notes were read first. They respectively cover joint main/input norm products and strong-unit substitution; discriminant shears; compositions including the strong norm; and auxiliary-ordinate translations. The present family preserves every factor and the complete polynomial exactly. It only changes the shared evaluation of two monomial coefficients.

At the independent cuts `(Delta,i,c)`, the actual old source has

```
c²           = c*c                  (already paid)
Ac2          = Delta*c²              (already paid by the main norm)
t            = i*c²
Q            = Delta*t²
K            = Delta*Q.
```

The last two are the ports `strong_difference` and `R16`. The strong norm is `f²−Q`; the auxiliary norm is `K*(V²−y²)+y²`. Together their four old coefficient gates are `t`, `t²`, `Q`, `K`. The old `t` and `t²` registers have no other consumers, while `c²` and `Ac2` remain live outside this replaced block.

The explicit family starts with five paid monomials `Delta,i,c,c²,Delta*c²`, all with coefficient1, and permits multiplication of any two available monomials, including a square. The two required outputs are

```
Q = Delta*i²*c⁴,   K = Delta²*i²*c⁴.
```

No addition, subtraction, division, coefficient change, coordinate substitution, norm replacement or finalizer change is permitted in this search. Exponents are nonnegative. A monomial exceeding the componentwise target box `(2,2,4)` cannot contribute to either output in such a circuit, so it can be omitted. A duplicate product need not be recomputed. Thus reachable sets of exponent vectors completely describe reachability in this bounded family.

The complete census has1,13,116,891 reachable sets after0,1,2,3 new multiplications, respectively. No set through depth3 contains both targets. There are21 successful fourth-gate transitions from one deterministic representative path per reachable depth3 set, yielding12 distinct terminal monomial sets. These numbers do not count all permutations or alternate derivations of every path. Deduplicating a state cannot affect later reachability because all future products depend only on the monomials already present.

A short independent explanation agrees with the census: `Q` cannot be obtained in two multiplications from the five starting ports, while `K` has a two-multiplication realization only through `H=i*(Delta*c²)` and `K=H²`. In a putative three-gate joint circuit, `Q` must be the third output and `K` must therefore be present by gate2. After that unique `K` construction, a single multiplication of the available monomials cannot produce `Q`: multiplying by `K` already exceeds Q's Delta exponent, and the missing complement to `H` is `i*c²`, which has not been computed. Four gates are sufficient, for example

```
t=i*c², H=i*Ac2, Q=t*H, K=H².
```

## Actual complete sources and proof

All21 representative successful schedules are inserted into the authenticated complete87 DAG and pruned from its final output. Every replacement monomial is checked by exact exponent addition starting from the actual `c²` and `Ac2` definitions. The two established coefficient identities are then used as cuts in a separate expression-DAG comparison of every one of the eight factors and the full product-minus-one finalizer. Every complete source remains **87=48M+39A**, uses exactly the original free ports, and has every emitted gate live. Fixed-coefficient multiplications, all factor multiplications, and the final subtraction of1 remain charged.

These literal identities prove that every emitted polynomial is **the same polynomial**, on every integer or rational tuple. The exact degree169, complete supplied positive zero set, ordinary-input semantics, compiler numeral/layout hypotheses and absence of an external horizon transfer without any new norm-sign or positivity premise. No witness is erased or reinterpreted.

The deterministic receipt contains all21 full circuits, ledgers, coefficient aliases, canonical schedules, state-set hashes and edge counts. It checks336 literal symbolic coefficient/factor/finalizer identities and672 supplementary full assignments, including336 signed assignments, totalling6,048 factor/output comparisons. Numerical fixtures are algebra checks; they are not materialized full universal Pell zeros. The first-root86 improvement lies outside the finite family and is neither challenged nor bounded by this census.

## Replay

The helper reads authenticated JSON/source bytes only and imports no historical compiler. Python3's standard library suffices. No repository file is written; output is written only to the explicit `--output` path.

```sh
python3 /path/to/complete87_shared_coefficient_scout.py \
  --root /path/to/native-stream-queue \
  --expect /path/to/complete87_shared_coefficient_scout.json
```

A fresh replay from `/` reproduced the saved receipt. Receipt comparison is recursively type-sensitive and `-O` execution is rejected. The five parent pins and helper SHA256 are in the receipt.
