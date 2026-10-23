# Wave-6 review at an exact source pin

Repository: VladimirReshetnikov/ProveIt.
Commit: `124c07c0b77a9e20e84676514d8b1ff78536ea3f`.
Root: `Computability/DiophantineConsistency/con-zfc-diophantine-forms`.
The package readmes, selected complete proofs and coefficient data are retained
byte-exact with Git blob IDs in `SOURCE_PINS.json`. No upstream script was run.

## Catalogue status

At this pin, packages 38--45 are already present but the collection README
still describes wave 5 and packages 31--37. `docs/incoming` contains only its
README, whose queue section still ends at batch 221 and says the queue is clear.
Thus neither root frontier table nor incoming queue text is an up-to-date
wave-6 comparison. The package-local readmes are the source for the following
claims; other than the coefficient checks separately listed below, the reported
degrees and operation counts have not been independently rederived here.

## Main claimed results

| Package | Primary ideas and claimed results |
|---|---|
| 38 batching11 | Direct quadratic multi-output coding; nine positive variables degree 166177600 / 864 operations (868 over naturals); ten integers 449607016 / 773; eleven positive variables 1154 / 123, or two-equation max-degree 1152 / 119 (118 shifted); optional 1140 / 129. Whole-label native tuple B=2^678139, 339476 raw bytes. |
| 39 direct10 | Direct B2 coding of 22 quadratics; ten integers 267823432 / 786. Separate complete compact instance with the same counts uses B=2^590069 and 295388 raw bytes. |
| 40 packing10 | Direct B2 coding, maximum weight 799; ten integers 237520456 / 782 on package31's complete tuple. Separate, explicitly incomplete factorized-receiver compiler candidate is not bound to its main equation. |
| 41 Bose--Chowla | B4 code on the quartic, largest weight610895; ten integers 69554088184 / 1333. Twelve positive variables 938 / 122, system929 / 117. |
| 42 additive-B4 | B4 code max942302; ten integers107286763576 / 2204, also coherently composed with nonzero-label tuple B=2^683195 /342269 raw bytes. P67 and system59 rebound to same tuple. |
| 43 Sidon10 | Direct B2 coding max799; ten integers237520456 /809 on package31's tuple. Same stated degree as40 but a more expensive evaluator. |
| 44 B4-sparse | Ten integers69554088184 /1407; nine positive23321536264 /1378; thirteen integers without Sun2026,226334238192 /1409; twelve positive901 /112 or905 /110. Coherent native B=2^590069 tuple295388 raw bytes, bound only to native P67/system59 in this package. |
| 45 multioutput | Own prior work: nine positive129875980 /788 (791 over naturals); ten integers237526776 /936; twelve positive941 /121, system932 /116. Direct quadratic targets and fixed-coefficient records. |

Domains matter: positive, nonnegative and unrestricted integer claims are not
interchangeable. An operation is a binary +, -, or multiplication, including
scalar multiplication; named registers do not increase the witness count.

## Frontier and substantive overlaps

- Package40's stated ten-integer degree237520456 /782 improves45's degree and
  cost. Package38 has a lower ten-integer cost773 but higher degree449607016.
- Own45 retains the best stated nine-positive degree and cost among38--45.
- Package38 is the only reviewed wave-6 moderate-degree eleven-positive form.
  Its strongest degree comparator is the optional translated product
  1140/129, not the main1154/123. Both are Pareto points. The optional
  shifted two-equation system is1138/124; the main shifted system1152/118.
- Package44's twelve-positive degree901 /112 dominates own45's941 /121.
  Package44's shorter-carrier905/110 and shifted three-equation896/104
  remain separate Pareto points beside the full-carrier shifted892/106.
- The native tuple in39 compact and44 is exactly the same integer tuple, not
  merely an equal base exponent. Independent reconstruction verified all four
  raw and deterministic-gzip hashes.39 already composes it with a direct-B2
  ten-integer equation, whereas44 uses it only for P67/system59.
- Packages41/42/44 use B4 quartic coding. Direct multi-output quadratic coding
  in38/39/40/43/45 is structurally stronger for these 22 quadratic residuals.
- None of these readme claims beats the historical67-operation scalar or
  59-operation system solely on evaluation cost. No new proof-assistant
  certificate or consistency decision is supplied by these packages.

## Checked coefficient contribution

The exact complement decoder replaces independent radix-four parity fields
with one bounded binary word. For Boolean selectors x_i, Boolean word W,
N<2^a, and 0<v_i<2^m, let

    S=sum_i [1+2^a(2^m-v_i)]x_i + 2^a W,
    mu=2^(a+m)-2.

The low selector field first forces zero or one selector; only then does the
bounded upper field force W=0 or W=v_i. Internal carries are intentional.
Putting the seven mandatory ones at the top makes selector coefficients small.
Here a=10,m=41,radix2^67,cell length8807 and padding prime581197.

The new independent checker reconstructs the tuple, verifies66,062 scalar
basis identities,38,663 single-bit mutations, both synchronization support
conditions, exact carry inequalities, mask populations and the actual-rank
controller. It finds no finite-data discrepancy. The ordinary universal
decoder proof and Boolean rank-control proof appear sound on inspection;
the inherited native-window/Pell and K215-calibration theorems remain imported.
See `NATIVE_INDEPENDENT_CHECKS.json`, `../coefficients/README.md` and the
portable 136-record coefficient-height certificate.

## High-value synthesis opportunities and cautions

1. Combine44's inner-separator removal with38's index-quotient absorption.
   The former excludes exceptional inner roots by Q dividing A(A-1) or
   (A-1)^2, contradicting0<A<sqrt(Q), and uses
   (Ig)^2-(cf)^2=I^2-c^2 for the outer separator. The latter removes h by
   absorbing divisibility into the existing carrier and proving a short
   Pell-index range. Reusing44's bounds blindly is invalid: its original
   estimate Ig-cf>1 invokes k>E, which is unavailable before h is recovered.
2. Use the strongest complete tuple for every newly proved family, rebinding
   all four ports and regenerating every derived fixed coefficient together.
   This is a justified synthesis, not a new coefficient-height record.
3. Sparse source support and separated target layout can improve direct B2
   positions further without requiring a full B2 set on all monomials.
   Exact target isolation must cover monomials not occurring in the source
   because they occur in the packed witness square.
4. Package40's factorized receiver candidate reduces selectors943→457 and
   support986→523. Its empty cells can retain payload bits, so native
   synchronization cannot be imported verbatim. An occupancy-first interface
   proof and possibly aggregate complement decoding could be valuable, but
   the package explicitly does not prove the complete compiler transfer.

## Errors and nonclaims

No mathematical error was established in the independently checked native
coefficient recipe. The known status problems are stale root catalogues,
scope differences in coefficient bindings, and40's explicitly open compiler
interface. Finite arithmetic checks do not certify the unbounded consistency
equivalence, Sun2026 remains an external theorem dependency where used, and
no global simplicity optimum is claimed.

## Actual variant ledgers

`VARIANT_LEDGER_CHECKS.json` independently counts and checks complete liveness
of the eight pinned main/optional38 and full/short44 product/shifted-system
DAGs. The degrees remain claims with inspected ordinary proofs, distinct
from the exact gate counts rederived in this review. In particular the
strongest degree1140 eleven-positive companion must not be omitted from
comparisons merely because it is not package38's headline result.

## Post-pin formalization update

The parent review additionally inspected merge
`2d7766807b92f6d505649885d472e20cc0236b4f`, after the construction pin.
Its exact documents and their own source ledger are under `postpin/`.
No source38--45 construction changed. The update adds executable supplied-data
Jones compilation, the full ScalarPR graph compiler, and a checked external
nine-variable ZFC endpoint whose coefficient selection remains existence-based.
Concrete `haltingTest` program extraction remains open. A useful integration
direction is to feed a certified sparse quadratic interface directly into
the new compiler rather than first form a quartic sum of squares. This is
an integration opportunity, not a completed formalization of the new equations.
