# Review: coercive Green certificates and connected well-conditioned computation

The mathematical claims in both reports pass this review within their explicit presentation and domain assumptions. Their exact finite-support witnesses are unbounded arrays, not fixed tuples of ordinary integer unknowns. The supplied finite polynomial compilers have externally selected support or horizon. Neither report reduces the maintained universal arithmetic-operation bound.

The original author suites pass: **110,522 checks** for Coercive Green and **38,524 checks** for Well-Conditioned Computation. All five example exports reproduce byte for byte. There are two concrete API defects in the Well-Conditioned implementation: exported row dictionaries alias the live certificate and can erase input binding, and prime deduplication can hide inexact scalar inputs. The isolated repair below resolves both, retains all formulas, passes the original suite, and preserves all valid exports byte for byte.

## Artifacts and coverage

The [portable checker](review_coercive_connected_aebfa386e.py) and its [deterministic receipt](review_coercive_connected_aebfa386e.json) pin these original archives and all members:

- `Coercive_Green_Diophantine.zip`: `8e2830036ad0a465f729d4729835b350ea288f758fd8bac8a3ac179ebe368d7a`.
- `Well_Conditioned_Diophantine_Computation.zip`: `9cd194e2d3b1cd7814ad465c1c4abae8966b6c7bb0b5a13d1955d17aba159258`.

I read the complete 1,500-line Coercive article and 1,491-line Well-Conditioned article, their READMEs and source audits, both Coercive Python modules, and the connected substrate and verifier. I read all proofs, including analytic, arithmetic, sparsity and compiler claims, rather than inferring them from test receipts. I checked the build commands but did not rebuild or visually review PDFs. No Lean/Rocq proof or numerical universal-machine table was independently reconstructed.

The checker safely extracts private temporary copies, pins bytes before imports or execution, rejects unsafe or duplicate archive paths, and runs the meaningful original entry points:

```
Coercive: python code/verify.py
          python code/green_machine.py --export-example examples
Connected: python verify.py
```

It normalizes only the Coercive receipt's reported Python version. The connected receipt is compared without normalization. It checks all original example bytes, then applies the pinned patch to a separate private copy and repeats the connected author suite and byte comparisons. Temporary imported review modules are removed and prior objects restored. The original archives remain untouched.

## Coercive Green: proof audit

The branch tags distinguish positive and zero branches even when their target states coincide. Appending a nonzero base digit makes the step map injective, while the strictly increasing history rules out cycles and infinite predecessor chains on **all** natural labels. The resulting graph is a disjoint union of finite paths and rays. History-zero sources are actual endpoints. No endpoint decision is hidden in the local neighbor algorithm.

The bounds for `L=αI−A`, `α≥3`, follow from adjacency norm at most two. The Neumann inverse is uniformly bounded and has the stated geometric tail. For sparse rational sources, a radius-K neighborhood in a path forest has only polynomially many labels, and label/coefficient bit growth is controlled, so the stronger polynomial-time approximation statement is justified here.

Inverse-column positivity proves that finite support is equivalent to a finite source component. The terminal normalization `H(u)=1` removes the arbitrary scale: a halting path with n configurations has the unique entire integer witness `c=D_n`, coefficients `D_(n−1),...,D_0`. The terminal functional is used only on finite support; it is not implicitly extended as a bounded Hilbert-space functional. The torsion-free ring extension is correct and stronger than characteristic zero. The report supplies a genuine modular counterexample and an additive-torsion characteristic-zero example; those qualifications are necessary.

The finite Green fraction and infinite-ray root satisfy the actual operator rows. Their strict separation, the continuant growth law, Pell descent and rational-level decision procedure all check. A specified rational level determines a finite path length effectively; rationality is the unbounded union of those levels and remains halting-complete. Efficient approximation does not decide equality to the irrational limit. The no-computable-cutoff argument controls support, charge and positive separation without assuming a physical exact measurement.

The polynomial-functional presentation explicitly pays in a different language: arbitrary finite polynomial support, typed zero-boundary maps, coefficient extraction and the fixed substitution `Z→Z^B`. Source data enter through monomial exponents. These operations and sorts have not been compiled into a bounded number of ordinary integer witnesses or a paid ordinary-input loader. Each ordinary supplied-support slice is a quadratic polynomial in `|E|+1` integer coordinates and at most `3|E|+2` residual squares. Including every exterior neighbor row is essential and the code does so. For each supplied E this is a finite decidable linear system; existentially varying E is the unbounded resource.

The shunted-network and killed-walk interpretations match the operator. The network is infinite and finitely presented, and the random walk has a uniformly bounded expected lifetime. The undecidable property is exact rationality of its response/expectation, not analytic solvability, almost-sure termination or finite-precision approximation.

Independent executable checks cover 720 additional history labels, 36 rational Gaussian-elimination inverse columns, 288 complete-coordinate mutations, 144 rational enclosures, and 12 exact exterior-leakage fixtures. They supplement the general proof, not an exhaustive test of all machines.

## Connected network: proof audit

The two rails, coupling hubs and backbone produce a connected computable graph of maximum degree three. The rail-swap involution makes a signed dipole source antisymmetric, so all hub and backbone voltages cancel exactly. The positive rail retains the original path recurrence. This proves the full integral fibre: every certificate is a positive multiple of the primitive continuant column, and its least charge is `D_L`. A nonnegative single-source column could not have finite support on this infinite connected graph; the Neumann positivity obstruction explains why the dipole is necessary.

The connected coercivity and energy estimates are correct. General neighborhood enumeration is only claimed computable, unlike the polynomial path-neighborhood claim in Coercive Green. The scalar source response can still be approximated from a bounded number of simulated path steps. Finite-support attainment on the dense rational/algebraic domain is distinguished correctly from existence of the unique Hilbert-space minimizer.

The finite-prime theorem concerns the **unit-source** solution. It does not allow a freely chosen denominator-clearing charge. For odd m, the rank of apparition follows from invertibility of the Lucas pair recurrence; divisibility follows from scalar powers of the 2×2 matrix. The binomial valuation proof correctly handles odd primes and separately uses `U_3=m²−1`, divisible by eight, at p=2. These give the explicit S-smooth length cutoff. The resulting decision theorem is specific to this family over a supplied finite prime set, not a decision theorem for arbitrary equations over localized rings. Allowing arbitrary charge already recovers the universal integral finite-support relation.

The row-sparsity theorem has the right quantifier order. Each **fixed** connected scalar operator with nonzero diagonal and at most three nonzeros per row has a degree-two support graph; endpoint/path type may be hardcoded. Finite-support solutions are confined to the interval spanned by source support and, on a ray, its endpoint, so a finite rational solve suffices. This is not a uniform algorithm deciding graph type from a presentation, nor an arithmetic-circuit lower bound or a statement about hidden block coordinates.

The bounded natural polynomial uses sums of squared linear residuals plus unsquared nonnegative routing cross terms. Natural one-hot selection, routed counters, guards, exact first halting, history and all electrical coordinates are forced. Its witness and residual formulas are correct. Naturalness is essential: signed all-value identity tests do not prove signed zero-set equivalence. The final halt and exterior-network obligations are both explicitly paid. The author already notes a possible projection of positive slacks; that observation is not a newly implemented operation improvement in this review.

Independent checks cover 350 node encodings, 1,400 connected vertices and involution equations, 16 full dipole certificates, 128 signed complete-polynomial expansion identities and 700 finite-prime length cases.

## Confirmed implementation defects and narrow repair

Original `well_conditioned_diophantine/src/substrate.py` lines 343–348 define a frozen `Certificate` containing mutable row dictionaries, then return the same dictionaries from `export` at lines 373–377. A normal export mutation therefore changes the live equation. Concrete fixture:

```
p = countdown()
cert = compile_certificate(p, 3)
w = canonical_assignment(p, (2,), 3)
w['x0'] = 99
cert.energy(w)                         # 9409
export = cert.export()
next(r for r in export['linear_residuals'] if 'x0' in r).clear()
cert.energy(w)                         # 0 in original implementation
```

This is loss of the actual initial-input constraint, not merely mutation of a display-only copy. It does not refute the mathematical compiler theorem or the original unmutated export.

At original lines 285 and 306, `set(primes)` runs before `is_prime` checks. `localization_bound(5,[2,2.0])` therefore accepts an inexact scalar because Python merges it with the exact integer 2. The arithmetic result for prime set `{2}` is unchanged, but the advertised exact-input contract is violated. Both input orders are tested by the repair regression.

The [isolated patch](well_conditioned_certificate_snapshots.patch), SHA-256 `cdd6307d5659ae0c72e7715b72e22e8692b07362d0a0f008f89a9ac85372f2a9`, changes only the reference API boundary:

- snapshot coordinate names and cross terms into tuples; copy and freeze each row with a mapping proxy;
- validate declared names and exact integer row coefficients on direct construction;
- return fresh row dictionaries from every export;
- require an exact Boolean for the natural/signed evaluation mode;
- validate every supplied prime before canonical set formation.

The resulting `src/substrate.py` is pinned at `7aec66923ff0137a57743842544909290b067bfb2bdd999541b40c6425d0d338`. The private repaired copy passes the unchanged original 38,524-check suite and regenerates all three connected examples byte-identically. The focused boundary suite includes 70 rejected calls and a constructor mutation check. The original wrong-input fixture now stays at energy 9409 after export mutation. Neither mathematical formulas nor valid witness counts change. The patch is delivered for review and has not been applied to the retained archive.

## Arithmetic-complexity implications and limits

The transferable mechanisms are exact normalization of scale, exterior-row checking, antisymmetric cancellation, and the explicit denominator recurrence. They make the finite-support representation precise but do not compress an unbounded support or history list into a fixed number of integers. The sharp row-four theorem counts entries of one fixed infinite operator under stated presentation assumptions; it is not a lower bound for universal Diophantine arithmetic operations.

A possible subsequent circuit optimization is exact factoring of the connected compiler's routing cross sum. Its already-generated selector sums and routed-counter sums can be shared when evaluating `Σ_(r≠s,j)b_s a_(r,j)`. That algebra does not alter natural or signed polynomial values, but an actual complete straight-line emitter and ledger would still be needed before claiming a new paid count. No such reduction is included in this review packet.

The primary [Dudenhefner record](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2022.16) confirms the instruction-set qualifications behind two-counter universality, and the [Doyle–Snell author record](https://arxiv.org/abs/math/0001057) supports the classical network/random-walk attribution. The new graph, coercivity, continuant, localization and sparsity claims were checked directly from their proofs. No exhaustive literature-priority audit is claimed.

## Reproduce

```
python review_coercive_connected_aebfa386e.py \
  --green-archive /path/to/Coercive_Green_Diophantine.zip \
  --connected-archive /path/to/Well_Conditioned_Diophantine_Computation.zip \
  --patch well_conditioned_certificate_snapshots.patch \
  --expect review_coercive_connected_aebfa386e.json
```

`--output PATH` saves a new deterministic receipt instead. Expected records are compared with recursive exact types. No helper depends on a permanent temporary-directory path or writes to an original archive.
