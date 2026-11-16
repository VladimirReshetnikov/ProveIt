# Mathematics in iPRA: finite demands, root supports, and norm certificates

Prepared for Vladimir Reshetnikov, 15 November 2026.

Start with `ipra_finite_demand.pdf`. The complete LaTeX source is
`ipra_finite_demand.tex` with the seven files under `sections/` and
`references.tex`.

Source baseline: ProveIt commit
`052fbaebfc955294b4c02f6532ab7e7a3f760f7a`.

## Contributions

1. **Backward demands and changing parameters.** A general finite-observation
   induction rule and a two-recursion implementation of
   `x(n+1,k) = F(n,k,x(n,D(n,k)))`. No monotonicity of the demand is needed.
   A nonlinear real-name example has the explicit input budget `K + 2N`.
2. **Aggregate witnesses.** Finite Hausdorff observations, a least-neighbor
   chain producing a PR point name, distances, finite images, and approximate
   optimization with explicit constants. The report states exactly which
   selection claims do not follow.
3. **Root supports through collisions.** Uniform finite rational deflation,
   a product-based perturbation theorem, and a PR root-support name for a
   monic polynomial with fixed PR coefficient names. This addresses the
   Puiseux report's representation obstruction by changing the output
   contract; it does not recover exact singular Puiseux coefficients.
4. **Automatic algebraic norm certificates.** A general monic-plane norm
   zero-count theorem and the exact weighted degree formula for
   `y^m = f(x)` with `gcd(m, degree f) = 1`. Proper weighted-evaluation
   subspaces consequently have at most `L` distinct curve points. This
   extends the earlier hyperelliptic geometric contract.

The written proofs identify fixed PR algorithms, explicit finite searches,
and bounded invariants. The root producer depends on the repository's
written rational-descent lemma; the original FTA article is included under
`dependencies/FTA_iPRA/` with exact provenance. No general Siegel/Faltings
height bound, arbitrary Mordell-Weil quotient representatives, global branch
labels, or multiplicity matching is claimed.

## Lean status

All five delivered modules compile with Lean 4.32.0 and `Std` only.

- `BackwardDemand.lean`: proved native scheduling, recurrence, transfer,
  and finite-query theorems.
- `FiniteHausdorff.lean`: proved native finite-checker reflection and cover
  combinators. The rational triangle instance inherits `Classical.choice`
  from standard rational-order lemmas; this is explicitly recorded.
- `AggregateTargets.lean`: concrete chain, distance and optimization
  programs, with named **unproved** propositions.
- `RootSetTargets.lean`: concrete descent clock, polynomial, factorization,
  root-support and sampled-adequacy definitions, with **unproved** targets.
- `NormTargets.lean`: concrete general monic-plane and superelliptic norms,
  finite points, subspaces and annihilators over rational coefficients and
  rational points, with **unproved** targets. The written theorem also
  treats coded fields; generalizing the Lean definitions is still pending.

There are no admitted proofs or custom axioms asserting the missing results.
Native theorems and compiled target definitions are not completed embedded
`Prf PRAAx` derivations. Sections 2–6 give the exact next definitions,
invariants, dependencies and repository APIs needed to build those proofs.

## Reproduction

With Python 3, Lean 4.32.0, and a normal TeX Live installation:

```sh
python3 build.py --lean /absolute/path/to/lean
```

If Lean is on `PATH`, `python3 build.py` is sufficient. `--skip-lean` and
`--skip-pdf` select the available parts; they do not imply that omitted
checks ran. Lean build intermediates are written under `.build/`.

The three standard-library Python programs can also run separately:

```sh
python3 code/finite_demands.py
python3 code/root_sets.py
python3 code/superelliptic_norm.py
```

The reference checks use exact rational arithmetic. They validate finite
implementations, not universal mathematical claims. The generic root grid
fallback has enormous worst-case bounds; the examples use certified
elementary shortcuts and then check their exact residuals.

## Contents and evidence

- `proof_status.json`: precise claim and implementation status.
- `lean/`: native proofs and concrete unproved targets.
- `code/`: exact reference implementations and checks.
- `validation/`: actual compiler output, axiom audits, code results and PDF QA.
- `provenance/`: selected source manifest, pinned paths, and review notes.
- `dependencies/FTA_iPRA/`: unchanged source and PDF for the one substantial
  inherited existence argument.
- `MANIFEST.sha256`: integrity hashes for the delivered files.

The review is targeted and does not certify every packet in the repository.
The package was prepared as a standalone deliverable; no upstream changes
are required to read or run it.
