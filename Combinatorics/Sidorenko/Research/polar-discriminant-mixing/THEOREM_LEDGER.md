# Theorem ledger and proof review notes

Article: *Exact restriction laws and Fourier cancellation on hyperbolic
quadrics*. References below use the article's stable LaTeX labels.

**Status convention:** “proved” means that a mathematical proof is written
in the article. It does not mean independently refereed, formally verified,
or certified historically new. Computational checks are additional evidence
on explicitly finite scopes, not general proofs.

## Classical inputs, rederived or explicitly attributed

| Topic | Article location | Status |
|---|---|---|
| Rank, radical, and discriminant classification; marginal probabilities `p_n`, `mu_n` | Section 2 | Classical; elementary derivation provided; Schmidt cited |
| Hyperbolic generator counts and intersection numbers | `lem:polar-geometry` | Classical; direct counting proof |
| Two Latin–Greek families and equal proper-subspace incidences | `lem:polar-geometry` | Classical; direct proof; Kiermaier–Schmidt–Wassermann cited |
| Symmetric-form full-rank Fourier transforms | `lem:fourier-recursion` and Section 8.1 | Elementary classical specializations; direct Gauss-sum recursion; not claimed as new association-scheme eigenvalues |

## Statements proved in this article

| Label / topic | Hypotheses and result | Computational coverage / limits |
|---|---|---|
| `lem:extension` | Any singular fixed common block over odd `F_q`; exact nonsingularity and character extension means | Every leading 1x1 and 2x2 block over `F_3` tested |
| Full rank/type transition, Section 3 | Complete transition using rank of a uniform rectangular mixed block | Proof supplied; no claim of exhaustive testing in all dimensions |
| `thm:joint`, `cor:kernels` | Exact joint-sign law for two subspaces, arbitrary dimensions and intersection; exact covariance kernels | All four sign choices in four `(r,s,t)` configurations enumerated |
| `lem:kernel-bounds`, `thm:profile` | Uniform covariance inequalities and exact arbitrary weighted intersection profile | Rational checks; arbitrary real weights in exact identity, nonnegative weights required for termwise upper bounds |
| `thm:polar` | Sharp all-generator character variance `q^(-(r-1))(1+O_r(1/q))`, `r>=2`; exact centering and sign/nonsingularity bounds | 96 `(r,q)` formula pairs; all `F_3^4` forms for `r=2` |
| `thm:grassmann` | Character variance exponent `n-r`, for `n>=2r`; explicit sign/nonsingularity bounds | 120 parameter triples |
| `thm:transfer` | Incidence sums are multipliers for lifted Fourier frequencies for congruence-invariant statistics | General written proof; basis independence included |
| `thm:top-rank` | All lower ranks cancel in a two-family contrast; exact top-rank energy identity | All generators in dimensions 4 and 6 used in selected checks |
| `thm:filter-rigidity` | Universal suppression of every rank below `r` forces constant opposite weights on the two full families | Written proof using rank-`r-1` incidence and connected adjacency; this is a weighted spectral formulation, not a new classical halving |
| `thm:contrast`, `cor:quadratic`, `cor:correlation` | Exact character, nonsingularity and individual-sign contrast second moments; quadratic exponent; family correlation | Exact Fourier checks at all nonsingular frequencies in dimensions 1–3 over `F_3`, and full four-dimensional contrast covariance |
| `thm:pointwise` | Even `r`: character contrast equals an explicit scalar times signed common-generator count `Z`; odd `r`: nonsingularity analogue | Even identity on all 59,049 `F_3^4` forms; odd identity on the specified 19,683-form slice in dimension 6 |
| Square-characteristic-polynomial obstruction, Section 9 | A common generator forces `charpoly(H^(-1)Q)` to be a square; hence necessary for nonzero contrasts in the stated parities | Checked for all 13,635 `F_3^4` forms with a common generator; converse to nonzero contrast is not asserted |
| `thm:rare-law` | Exact common-generator moments; `P(Z!=0)=(2+O_r(1/q))q^(-r)` and `P(Z=+1)=P(Z=-1)=(1+O_r(1/q))q^(-r)` | Exact moment formula checks and full `r=2,q=3` histogram |
| `cor:non-gaussian` | Variance-normalized even-character / odd-nonsingularity contrast converges to zero in probability in specified large-parameter limits, despite second moment one | Proven via support probability, not inferred from a histogram |
| `thm:rank-two-law` | Complete five-point `Z` law for `r=2`, every odd prime power | Direct proof via bidegree `(2,2)` polynomials; exhaustive `q=3` histogram |
| `lem:conditioning` | Coarse conditioning bound for one or two nonsingularity constraints | Does not assert unchanged conditional means or covariance |
| `lem:pencil-conditioning`, `cor:conditional-polar` | Relative bounds for observables invariant under `Q -> Q+aH`; leading polar moments preserved under a fixed finite pencil of invertibility constraints | Translation invariance is essential; not applied to all Grassmannian restrictions |
| `thm:local` | Local rank-layer transverse error `O_r(q^(-1))` for `r>=3`; two-active case for `r>=2` | Full parametrization and conditional law proved; not a global Sidorenko audit |

## Points checked in the proof review

- The statistic `D(C)` is zero on a singular matrix. Quotient discriminant
  signs are introduced separately only where the common-block extension
  proof requires them.
- Determinant characters are basis-independent because basis changes
  multiply determinants by squares. Odd characteristic is used in the
  trace pairing, Gauss sums, and hyperbolic reduction.
- Two restrictions are conditionally independent after fixing their
  common block. Three arbitrary restrictions are not assumed to be so.
- Singularity of the common block is not discarded; the full-row-rank
  probability of the rectangular mixed block accounts for its repair.
- The variance of an individual sign indicator is not the variance of
  determinant character. Exact means and cross covariances are retained.
- The two-family contrast is not a statement that each family is close
  to `1/2`: finite-field bias and common fluctuations remain.
- The full-rank Fourier factor is constant on rank/type orbits, which
  permits the incidence cancellation. No arbitrary non-invariant statistic
  is silently substituted into that theorem.
- Universal full lower-rank cancellation is already classified by the
  filter-rigidity theorem; the further signed-design question asks about
  partial cancellation, not the case already solved.
- A square characteristic polynomial is a necessary obstruction, not
  a sufficient certificate of a nonzero signed common-generator count.
- In even-character and odd-nonsingularity parity, variance comes from
  rare jumps. A Gaussian limit is not asserted and is ruled out for the
  variance-normalized laws considered.
- Conditioning does not preserve the unrestricted Fourier law exactly.
  The sharper relative result uses invariance along pencil lines, and
  requires `q > n * number_of_shifts` for its displayed bounds.
- The pencil-conditioning comparison preserves squared-contrast expectations
  relatively; it does not assert relative preservation of a mixed contrast
  covariance (which can vanish without conditioning).
- In the local application, the matching indicator stays inside the
  expectation. No uncontrolled further conditioning on the sign match
  occurs. The `r=2` triple case is not included in the improved local rate.
- Fixed-rank asymptotics are distinguished from bounds uniform in rank.
  The exact contrast formulas themselves apply for every stated `r,q`.

## Deliberately unclaimed

No historical-priority certification, independent referee approval,
Lean verification, global Sidorenko verification, global Szemeredi-bound
improvement, or exhaustive review of either repository is claimed.
No general distribution theorem is asserted for odd-character or
even-nonsingularity contrasts, or for the ordinary all-generator average.
The nine research questions identify these and other next steps.
