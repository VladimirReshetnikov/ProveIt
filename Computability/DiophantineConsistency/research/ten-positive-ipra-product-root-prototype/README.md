# Doubled product-square root extraction in IΣ₁ models

This author-checked prototype joins the separate [`TenPositiveDoubling`](../ten-positive-ipra-doubling-prototype/README.md) and [`ScaledSquare`](../ten-positive-ipra-scaled-square-prototype/README.md) lemmas. For arbitrary elements of any `IΣ₁` model with the repository's `ORingStructure` interface, write `a=delta*U²*E`, `G=E*(1+a)`, and `Q=delta*((1+4*a*(1+a))-1)`, with model truncated subtraction. Assuming `delta,U,E,V0,M>0` and

`(Q-1)*z² = M²*G*(Q*V0²-1)`,

`doubled_product_root` produces a model square root of `G`, and `doubled_product_roots` produces **positive** roots `tau,f` such that `E=tau²` and `1+a=f²`. The intended `V0` is the positive magnitude of the signed quantity called `V` in the ten-positive ordinary proof; this theorem takes `V0` as an abstract positive model element.

The proof obtains a Bézout certificate for `G` against `(Q-1)*(Q*V0²-1)` from the doubling coprimality theorem using the internal gcd, then invokes the scaled-square factor theorem. It splits `G=E*(1+a)` with the explicit Bézout certificate between `E` and `1+a` and the existing model coprime-square theorem. It neither assumes `M∣z` nor uses prime factorization or unique factorization. The Lean metatheory's axiom report should not be confused with iPRA axioms.

This is still **conditional abstract model arithmetic**. It does not prove that a zero of either 84/436 or 85/328 ten-positive graph supplies the displayed relation and positivity, interpret either graph or its ports, complete adjacent-Pell descent, establish either direction of machine equivalence, or prove an internal iPRA endpoint. It is not a theorem about a PDF. The 13-variable `adaptive-gap85` is a different candidate.

Attempt 01 checked the preceding single `G`-root statement. Author attempt 02 checked the current three statements with exit 0, empty stderr and no warnings; snapshots, commands, hashes and resource samples are in `observations/attempt02/`. All three printed axiom reports are `[propext, Classical.choice, Quot.sound]`. Current source SHA-256 is `c3fd25ceb22e7bfbf899005f954a60b40618746301bbb5bc0ab861e078ecf0e7`; output object SHA-256 is `92dbb47e969d3603f6f496f53c7995493a989293a37e5272c308ff79d3fb09d5`.

The runner pins both separate prototype objects and the selected direct `ArithmeticGcdNormalization` object before and after, along with source, runner and Lean executable. It inherits the selected 90-operation project provider and does not independently rehash its complete union, package-transitive or dynamic libraries, or establish full historical source-to-object ancestry. Sampling is not continuous and `/tmp` paths may disappear. This is not a paired replay.

Run from the repository root with a fresh attempt name and a free guarded Lean slot: `ATTEMPT=attempt03 python3 -I -S -B Computability/DiophantineConsistency/research/ten-positive-ipra-product-root-prototype/run.py`.
