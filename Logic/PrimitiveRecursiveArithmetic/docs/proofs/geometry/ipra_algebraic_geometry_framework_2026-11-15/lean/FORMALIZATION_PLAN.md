# Lean formalization plan

## Status

The `.lean` files in this directory are source-level blueprints. The preparation environment had no Lean executable or local ProveIt dependency closure. They are **not claimed to compile** and contain no `axiom`, `sorry`, or `admit`. Universal results are represented as named target propositions or comments, not silently asserted theorems.

## Two layers

1. **Semantic host layer.** Replace mathematical quotients by `CertSetoid`, and represent equality by a checked witness. This is the layer sketched in `CertifiedSetoid.lean`, `PresentedAlgebra.lean`, and `ProjectiveCech.lean`.
2. **Object-iPRA layer.** Replace every host function by one fixed `ConciseIPRA.PR` code; express its graph or Boolean checker using `PTm` and `Fm`; construct a derivation of type `Prf PRAAx`. Only then apply `pra_iff_native`.

## Dependency order

1. **Codecs.** Natural-number codes for signed integers, finite lists, exponent vectors, sparse/dense polynomials, Laurent polynomials, matrices, and witness vectors. Prove bounded access and reconstruction.
2. **Finite algebra.** PR addition, multiplication, substitution, coefficient folds, exact polynomial identities, and module linear combinations. Construct `Prf PRAAx` proofs of their defining equations and congruence.
3. **Certified setoids.** Encode `Valid(x)` and `EqW(x,y,w)`. Prove witness transformers for reflexivity, symmetry, transitivity, and operation congruence. Equality is not Booleanized by searching for a witness.
4. **Presented quotient rings.** Implement the checker for `p-q=sum h_i g_i`. Prove soundness coefficientwise. Derive quotient-ring laws by transforming the multiplier list.
5. **Localization.** Encode `(a,n)`. For equality use a witness `(k,w)` checking `f^k(f^m a-f^n b)=0`. Prove transitivity with an explicit exponent and combination; prove congruence of addition and multiplication.
6. **Power-cover constructor.** Given `sum c_i f_i=1` and `N>=1`, set `M=r(N-1)+1`, enumerate weak compositions of `M`, assign each term to the least coordinate at least `N`, and factor `f_i^N`. The invariant records the partial multinomial expansion and the assigned coefficient lists.
7. **Principal-cover uniqueness.** Take the maximum of the local annihilation exponents, call the power-cover constructor, and combine the local zero witnesses.
8. **Principal-cover existence.** Homogenize denominators; take the maximum overlap-killing exponent; obtain cross identities at one common power; construct power-cover coefficients; output `m=sum d_i b_i`. Prove `f_j^q m=b_j` by a bounded double fold.
9. **Finite affine atlases.** Encode charts, principal overlap pieces, localization maps, inverse witnesses, and triple-overlap cocycles. Define morphisms and refinements as finite certificate families. The gluing theorem from steps 7–8 supplies the structure-sheaf and quasi-coherent-module equalizer laws.
10. **Projective line.** Encode the two charts `R[t]`, `R[u]`, the overlap `R[t,t^{-1}]`, and `u=t^{-1}`. Encode `O(d)` by transition multiplier `t^d`. Prove the high/low/middle Laurent split and obtain the `H^0` and `H^1` normal forms.
11. **Projective n-space.** Encode subsets of `{0,...,n}` and exponent vectors. Decompose the finite Čech complex by exponent vector. For mixed signs, choose the least nonnegative coordinate and verify `hd+dh=id`; the all-nonnegative and all-negative cases give the two surviving degrees.
12. **Native transport and audit.** Produce the actual `Prf PRAAx [] ...` values, inspect axiom dependencies, and transport them with `pra_iff_native`. Do not label a theorem formalized before this step.

## Principal formulas to expose

The concrete formula names may change with the repository codec library, but the final module should expose:

```lean
powerCoverFormula              -- checked output satisfies sum d_i f_i^N = 1
principalCoverUniqueFormula    -- restrictions jointly monic
principalCoverGlueFormula      -- compatible local fractions have a global section
localizationTransFormula       -- proof-relevant equality is transitive
p1LaurentSplitFormula          -- c = delta(a,b)+middle, with d<support(middle)<0
p1OGlobalFormula               -- Gamma(P^1_R,O)=R
p1OdCechFormula                -- H^0/H^1 normal forms for every d
pnOdCechFormula                -- standard-cover cohomology table
```

## Induction audit

Every induction is over a number controlling a finite list, exponent, monomial enumeration, matrix row, or subset enumeration. The invariant is a conjunction of PR equalities/inequalities and accepted certificate checks, hence quantifier-free after introducing accumulator terms. Assertions about all local pieces are handled by Boolean prefix folds; no induction formula quantifies over ideals, prime spectra, sheaves, or represented reals.
