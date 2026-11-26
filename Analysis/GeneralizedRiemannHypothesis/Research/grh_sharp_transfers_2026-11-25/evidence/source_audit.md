# Source audit of `lsernau/grh-lean`

## Frozen source and scope

The fetched GitHub commit and local shallow checkout agree on
`72fead102f663d5c7a407964a13dc0cf9d977207`, authored 2026-11-25 at 20:38:07 UTC.
The readable project pins Lean `v4.35.0` and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
Its five externally advertised statements occur in `grh/src/Statements.lean`
and `grh/src/Main.lean`. The former imports only Mathlib. They are RH, a
version identifying all nontrivial zeta zeros, Dirichlet L-function
nonvanishing for Re(s)>1/2 with the principal pole excepted, zeros on the
line in the open critical strip for all Dirichlet characters, and the
primitive-character specialization.

This is **Dirichlet-GRH**. The stated results do not quantify over arbitrary
number fields, Hecke characters of such fields, Artin representations, or
automorphic representations. Extending the *method* to these would require
new input, even while accepting all five conclusions as established.

Canonical repository URL:
<https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207>.

## Evidence checked here and its limits

The complete repository was cloned. The readable `src` directory contains
803 Lean files and 477,124 physical source lines. All 803 files lie in the
file-import closure of `Main`; this is not a declaration-level proof
dependency count. A reproducible lexical scan is supplied. It removes
nested comments and strings and searches for explicit `sorry`, `axiom`,
`admit`, unsafe and native proof escapes, and custom elaborator/macro
keywords. No such tokens were found in the initial readable-source scan.
The authoritative two-edition result is in `source_scan.json`.

`Challenge.lean`, outside `src`, intentionally contains five `sorry`s for
Comparator and is excluded from the default targets in `lakefile.toml`.
It is not imported by `Main`. Its existence is not evidence of a hole in the
actual theorem proof.

The repository README reports clean Lean builds, three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`), and independent replay using
nanoda, con-leche, con-ron, and Comparator. Those are the author's reported
checks. This session did not independently replay them: `lean`, `lake`,
`elan`, and the independent checkers are absent from the runtime. Source
inspection is not a substitute for kernel replay. The README also says no
mathematician has read through the proof and no paper accompanies it.

## Reusable architecture, with exact declarations

The following paths are relative to `grh/src/` at the frozen commit.

| Interface | Declaration and location | Mathematical content |
|---|---|---|
| Many short integral source vectors | `New.Data.span_short_integralRamified_eq_top`, `New/Reduction/ShortAndEnough.lean:254` | Integral forms whose normalized Poincare images have controlled lifted norms span the source. |
| Controlled denominators/index | `New.Data.indexLe_normalizedPoincare`, same file, line 373 | Images of selected translates have bounded integral index; the error is charged per source dimension. |
| Enough independent images | `New.Data.enough_forms`, same file, line 448 | A small set of translates spans at least `(1-4/b^2)` of the target dimension. |
| Lower determinant estimate | `New.Data.integral_forms_long`, `New/Determinant/Twist/LongForms.lean:214` | For an almost-full independent family, covolume `c` and index `delta` satisfy `c+2 delta >= dim*(mainAmount-3 f a log^4 b)`. |
| Cancellation | `New.star_inequality`, `New/Reduction/MainInequality.lean:87` | Compares the two estimates for the same lattice, cancels the main term, and proves `m*totalRemainder <= f*a*log^5 b`. |
| Prime-sum estimate | `New.Data.primeRemainder_le`, `New/Reduction/OneSidedBound.lean:33` | `R_q(x) <= phi(q) log^6(b)/m + abs(R_q(x1)) + log(b)*abs(R_1(x1))`. |
| Square-root exponent | `New.eventually_primeRemainder_natCast_le`, same file, line 125 | Taking `m` of order `sqrt(x)` gives `R_q(x) <= (64 phi(q)+3) x^(-1/2+6 epsilon)` eventually. |
| Pole dictionary | `New.isPolar_primeRemainder`, `New/Reduction/Zeros/PrimeError.lean:414` | The Laplace transform's residue is a weighted difference of zero multiplicities, divided by `s(1-s)`. |
| Auxiliary twist choice | `New.exists_entireL_quadTwist_ne_zero`, `Lib/Analytic/QuadraticTwist.lean:796` | Given beta>1/2 and finite height H, choose one prime d in a prescribed class so every relevant quadratic twist has no zero in the rectangle. |
| One-sided Landau theorem | `New.IsPolar.landau`, `Lib/Analytic/Landau.lean:217` | Eventual upper control of a real error and nonnegative residues on the real line force all poles in the right half-plane to disappear. |
| Final analytic criterion | `New.LFunction_ne_zero_of_primeRemainder_le`, `New/Reduction/Zeros/Criterion.lean:37` | Bounds for all primes d in the class combine with the chosen twist to exclude untwisted zeros. |

Here

    R_q(x) = sum_{n<=x, n=1 mod q} Lambda(n)(1-chi_d(n))(1/n-1/x)
             - log(x)/phi(q) - c_{d,q}.

The weights are nonnegative. However, the useful conclusion is only a
one-sided upper estimate for the *centered* remainder. Its transform has
residue

    [sum_chi ord_s E_chi - sum_chi ord_s E_{chi*chi_d}]
      / [phi(q)*s*(1-s)],

where `E_chi` removes the principal pole. Choosing the twist to have no
zeros in the relevant rectangle removes cancellation by the second sum.
For real s in (beta,1), the remaining denominator and zero multiplicities
have the required signs; for real s>=1 there are no remaining zeros.
Landau then eliminates the pole at the hypothesized complex zero.

This decomposition shows precisely what a transfer must replace: a
nonnegative prime detector; an arithmetic construction yielding the
correct one-sided bound; meromorphic continuation with a controlled pole
dictionary; and an auxiliary family that can remove opposite-sign poles.
The last item is not automatic for a new L-function family.

## Determinant and twist interfaces that may transfer independently

`New.exists_isRegularFamily`
(`New/Congruences/FitTwistsExist.lean:517`) produces a family with one
twist for each prime and complex-to-p-adic isomorphism. The relevant
denominator losses sum to the prescribed `denominatorBudget`. The result
does not select one globally best twist for all primes.

`New.Selmer.exists_rootsOfUnity_ellVal_eval_le_add`
(`New/Congruences/Selmer/RootsOfUnity.lean:474`) is a particularly clean
standalone interface. Given a dimension ceiling, a positive interior
radius, a bound on the sum of witness valuations, and epsilon>0, it first
chooses a common p-power torsion-order ceiling. Only then are an arbitrary
finite collection of integral polynomials and their individual witness
points supplied. One torsion tuple approximates every witness valuation
from above with additive loss epsilon. Degree is unrestricted, but the
sum-of-witness-valuations budget is essential. The quantifier order, the
common tuple, and the bounded order are more informative than mere
torsion nonvanishing. Previous ProveIt work has already strengthened this
interface, so it should be cited as an antecedent rather than rediscovered.

`New.Selmer.exists_anticyclotomic_twist`
(`New/Congruences/Selmer/GeneralTheorem.lean:392`) realizes the polynomial
selection in arithmetic: a single character and its first m powers all
have Selmer lengths at most beta_T+epsilon, bounded special-value
valuations, and small tame-generator losses. The bound beta_T is not zero.

## Barriers against overclaiming new conjectures

1. **Selmer/BSD barrier.** `SelmerDatum`
   (`New/Congruences/Selmer/SelmerData.lean:105`) explicitly assumes a
   finite global congruence term, finite local terms, a residual
   irreducibility condition in spanning form, a local dimension bound,
   and a special inertial scalar with `zeta^2-1` a unit. The global term
   is the supremum of lengths of conjugate Tate-dual congruence Hom
   modules (`conjDualHom`, line 63; `congruenceTerm`, line 77). Generic
   elliptic-curve or self-dual motive data cannot simply be substituted.
   The resulting inequality `length <= beta_T+epsilon` is not a
   Selmer-vanishing statement.

2. **Cyclotomic/Vandiver barrier.**
   `New.exists_length_shaOdd_le` (`Lib/Cyclotomic/OddSha.lean:645`) gives
   one nonzero integer X with
   `X <= 2^(4*(N+t+3)^27)*h_E`, whose valuations bound finite-level odd
   cocycle lengths for a CM subfield E of Q(mu_N). The source explicitly
   says these are cocycle modules, not quotients by coboundaries, and
   does not establish a comparison with a standard Sha group or an
   equality of characteristic ideals. For exponent zero it is the
   everywhere-unramified Hom module, without the nonzero-exponent parity
   condition. Thus neither Vandiver nor an Iwasawa main conjecture is
   a corollary of this interface alone. Any comparison supplied by an
   earlier ProveIt report must be used as an additional theorem.

3. **Artin/Hecke barrier.** The final statements are only Dirichlet
   characters over Q. Higher-dimensional positive-character detectors
   or Dedekind-zeta identities can formulate a transferable analytic
   criterion, but do not supply the determinant lower bound or the
   zero-separating twist family. A conditional criterion must remain
   conditional until those inputs are proved.

4. **Spanning and scale barrier.** A bound on one determinant or one
   nonzero form does not replace `enough_forms`. The arithmetic argument
   controls an almost-full-dimensional family while keeping index loss
   and the cost of completing a basis small. The square-root exponent
   depends on `m` growing as sqrt(x), not on a fixed-rank calculation.

## Reproduction

`scan_source.py` plus `source_scan.json` records a complete source-only
inventory, SHA-256 for every Lean source file, and the file import
closure. For independent proof replay use a fresh checkout at the pinned
commit and the commands from `grh/README.md`:

    cd grh
    lake exe cache get
    lake build
    lake env lean scripts/PrintAxioms.lean

The initial clone and checked files are in the shared working directory;
no repository was modified or published.
