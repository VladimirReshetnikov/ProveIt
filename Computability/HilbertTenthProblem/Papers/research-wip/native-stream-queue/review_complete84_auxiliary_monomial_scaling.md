# Independent review of the separated auxiliary monomial-scaling bound

**PASS within the stated separated grammar. No change requested.** The unbounded exponent argument proves at least **7 nonconstant multiplications and 3 binary additions/subtractions** for the three required outputs. The complete attaining circuit remains **84=47M+37A**, with 18 positive witnesses and the same polynomial as the parent. This is not a lower bound for arbitrary arithmetic circuits or for the full universal polynomial under other producer interfaces.

## Frozen artifacts and read scope

| Reviewed artifact | SHA-256 |
|---|---|
| [Author source](complete84_auxiliary_monomial_scaling.py) | `643ca33730e8b1e43088240c8f81dd72fbb6dc87506206c55ab5fda411bf2390` |
| [Author receipt](complete84_auxiliary_monomial_scaling.json) | `851d6339e1e8ab940f977b9177eef804fa6f45601c06f974412d0567267c4ae1` |
| [Author proof](complete84_auxiliary_monomial_scaling.md) | `db05c735b61b3165897430ed78f9a2d3967beb8f3c89044e7d5a29d4a9d79ffe` |

I read the complete author proof and helper, both full arrays and certificate data in the receipt, and the complete [84-operation parent proof](complete84_scaled_strong_output.md). I authenticated all three declared parent dependencies: Python `8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737`, JSON `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`, and Markdown `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade`. Predecessors were read as inert data; no predecessor program was executed or imported.

Fresh normal and optimized exact receipt replays of the new helper from working directory `/` both passed. Its parser rejects duplicate keys and nonfinite JSON values; comparison is recursively type-exact, and checks do not disappear under `-O`.

## Independent lower-bound challenge

The paid monomial set includes the constant, the six formal variables Delta,c,i,f,T,R, and the actual dependent monomials c² and Delta*c². It does **not** include f². The argument correctly retains those dependencies, rather than treating Ac2 as an unrelated generator.

In the monomial-production phase, an ancestor of a required monomial must divide it. After removing scalar duplicates, every useful multiplication ancestor is a new nonconstant monomial. The additive output phase cannot create a previously absent monomial exponent. The outputs therefore require the production of cTf, Rf² and Delta²*i²*c⁴ individually, even if they are eventually embedded in linear combinations.

Each of these three monomials is absent from the supplied set and from every product of two supplied monomials. Each consequently needs at least two multiplication gates. Their pairwise gcds are f,c,1, whose divisors are already supplied. Thus no useful multiplication gate can belong to two of these three ancestor cones, and their combined requirement is at least six distinct gates.

For every nonnegative exponent vector of the multiplier M, the further required monomial M*Delta*f² has both a positive Delta exponent and a positive f exponent. No supplied monomial or ancestor of any of the preceding three targets can have both. It therefore requires at least one additional product outside those cones. This proves the seventh gate uniformly for all exponents; no finite exponent enumeration is substituted for this argument. The other strong monomial M*Delta²*i²*c⁴ can only add requirements.

The additive lower bound is independent of the number of monomial products. V has three distinct monomials, all with Delta exponent zero. Both strong-output monomials have positive Delta exponent, remain distinct after multiplication by M, and hence have support disjoint from V. With two binary additions, V would need the second addition and the first would have to supply the other nonmonomial output. One further monomial cannot remove both terms of that first sum and produce V's three disjoint terms. Free scalar weighting changes no support. Thus three additions are necessary.

These arguments apply to the specified multiplication-then-linear-combination model. They do not exclude multiplying a nonmonomial sum later, changing Q, using additional paid relations or registers, or changing coordinates. In particular the six formal core variables are independent for this local theorem apart from the two explicit paid monomial dependencies; the theorem does not silently exploit or prohibit every other relation in the full source.

## Independent source and identity checks

Fresh standard-library data checks, separate from the author helper, reconstructed the exact two-row edit and examined all 168 rows of the parent and attaining arrays. Both have the same free and witness interfaces, closed topological order, all rows and ports live, and exactly 47 multiplications plus 37 additions/subtractions.

The actual consumer map confirms that the ten-row cut has only the three externally used outputs V,Q,S. The f² producer has no external consumer; c² and Ac2 are paid outside the cut with their stated definitions. The old `Tf-1` intermediate has only its private c-multiplication consumer.

Independent sparse exponent arithmetic expanded the actual cut with c² and Ac2 already specialized to their monomial definitions. It verified four local identities, including

    c*(Tf-1)=cTf-c,
    V=cTf-c-Rf²,
    Q=Delta²*i²*c⁴,
    S=Delta*f²-Q.

Every other retained row is literally unchanged. The local equality therefore propagates through all seven factors and the complete finalizer by induction on the actual source order. This proves the whole-polynomial identity on all supplied values, not just at positive zeros. The parent's uniform exact degree187 and positive-zero semantics transfer through that identity; this review did not rerun the historical degree or universality suites.

The independent fixed-premise check used the nine supplied exponent vectors and their 81 ordered pairs, obtaining exactly the gcds f,c,1 and the mixed-Delta/f support exclusion. These finite checks authenticate the premises of the unbounded proof. The author's sixteen complete signed evaluations are supplementary arithmetic checks, not positive compiler-zero fixtures.

## Scope of output scaling

The identity P_other*(M*S)-M*Delta=M*F84 is exact. On the valid positive compiler domain, a nonzero scalar monomial in Delta,c,i,f,T is nonvanishing, so multiplying the whole output by it preserves zeros. Allowing R formally in the exponent theorem does not establish its off-zero nonvanishing; the author correctly makes no corresponding positive-zero equivalence claim for R-scalings.

Only M=1 is emitted as a complete attaining source. The no-saving conclusion is confined to the stated family with the other producers and finalizer structure retained and the permitted local inputs fixed. General mixed arithmetic, simultaneous auxiliary-coefficient changes, and complete-circuit optimality remain outside the result.
