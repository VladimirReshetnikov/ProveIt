# Proposed ProveIt integration

Reference snapshot: `b7667ae40a2957eed9a53d8559d53a3ee20dd1c1`.

## Mathematical placement

The package is modular so that the proof-bearing parts can be integrated
without importing the standalone article's document class or page style.

| Package section | Suggested destination or role |
|---|---|
| `02_laurent.tex` | Shared height-one Laurent normalization; reconcile with the existing Barnes lemma |
| `03_gamma.tex` | New Gamma–polygamma normalization subsection near the harmonic/Gamma chapter |
| `04_scalar.tex` | Scalar Appell normalization and inverse-Gamma finite-part corollary |
| `05_fifth.tex` | Fifth-power continuation of the quartic digamma bridge |
| `06_calculus.tex` | Derivative and normalized primitive consequences |
| `07_tail_rank.tex` | Finite-prefix theorem following the inherited all-even-tail moment formula |
| `08_audit.tex` | Literature/convention notes and the narrow Young sign correction |
| `09_questions.tex` | Updated exact-identity research programme |

Preserve theorem labels or rename them systematically during the merge.
The standalone article defines its own theorem environments and operators
in `article.tex`; use the manuscript's equivalents on integration. The
symbols C_m in the tail section and calligraphic C_m in the Gamma section
are intentionally different objects. Do not collapse them into one macro.

The fifth-power section is self-contained for its residue argument. Its
short height-one Mellin discussion can be replaced by a cross-reference
to the shared normalization lemma when consolidating duplicate exposition.
The inverse-Gamma finite-part corollary uses the ordinary Gamma trace,
the degree-zero integral 1, and the degree-one finite part gamma.

## Exact source-question updates

The source is `ProveIt_Quartic_Tails_Resolvents_2026-10-11.zip`, member
`sections/research_questions.tex` under its top-level package directory.

1. **Question 1, fifth power:** mark its requested calculation as proved.
   Cite Theorem `q5:main`, Lemma `q5:constants`, the exact finite ledger,
   the endpoint table, and `results/fifth_exact_results.json`. The new
   mixed combination is J'(1). No independence or smaller constant
   reduction is implied.
2. **Question 2, canonical scalar polynomial:** record partial progress.
   The unique scalar residue normalizer is P_m(Y)=m![t^m]Gamma(1-t)exp(tY),
   up to an additive constant. Its finite decaying defects are explicit.
   The exact differential family isolates one height-one coordinate in
   an ordinary integral. The stronger scalar arithmetic-elimination
   assertion remains open.
3. **Question 8, finite generation by initial moments:** mark the stated
   existence-and-inverse question as proved. For even p<q, use
   N=q(q-p)/2+q/2+p-1 and moments D_0 through D_N. For p=q, use
   N=q-1 and the exact determinant. Retain the first-q assertion for
   every unequal pair as a stronger open optimization question.

The manuscript S6 and revised S8 candidates retain their existing status.
The already proved Choi harmonic conjectures and S4 identity require no
new claim from this package.

## Coefficient and cutoff conventions

- Z_d uses strict decreasing positive integer indices.
- lambda_d is the literal coefficient [u]Z_d(1+u,1,...,1).
- lambda_1=-gamma_1 in the conventional Stieltjes notation.
- eta=lambda_2, theta=lambda_3, xi=lambda_4.
- All coordinate finite parts use the lower cutoff epsilon in x itself.
- Gamma C_m integrals for m>=2 are ordinary convergent integrals.
- Formal matrix rank q does not assert rational independence of actual
  zeta or Stieltjes coordinates.

Young 2024, Eqs. (4.1)–(4.2) and Corollary 3, use the conventional signed
first Stieltjes constant while describing it as the literal linear
coefficient. Correct the description or translate consistently:
nu_(0,d)-nu_(-1,d-1)=c_(d+1)-lambda_d. Retain the numerical formulas
when their constants use the conventional alternating-sign definition.
The author’s July 2023 lecture explicitly confirms that sign convention.

## Prior-art attribution

Credit Sesma 2017 for the Roman harmonic generator and harmonic Bell
polynomials, Coffey 2011 for the degree-two ordinary integral, and Young
2023/2024 for height-one Laurent data and the Cauchy coefficient series.
The article proves the functional residue organization and its new
applications directly. It does not claim that the Gamma quotient or the
known coefficient series was first discovered here.

## Verification and editorial gate

Run `python3 verify_all.py` and build the article before moving sources.
The exact finite checks complement the analytic proofs. Run `--full` if
fresh numerical diagnostics are desired. The numerical records contain
no interval certificates; do not relabel their residuals as certified
error bounds. Preserve `claims.json`, the source snapshot and source
member hashes alongside imported verification scripts.
