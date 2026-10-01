# Arithmetic Rigidity off Resonance
## Exact convolution factors of geometric-uniform laws

Research manuscript prepared for Vladimir Reshetnikov, 30 September 2026.

The package contains a standalone article, complete written proofs, nine further
research questions, and exact finite arithmetic certificates. It extends the
Fabius/Rvachev convolution-divisor program in ProveIt to rationally separated
source scales and to prime-power rational-return channels.

### Files

- `article.pdf`: the compiled 24-page article.
- `article.tex`: the standalone LaTeX source, including its bibliography.
- `code/verify.py`: standard-library Python certificates and regression tests.
- `results/verification.json`: the delivered successful verification receipt.
- `results/verification.log`: console summary from the delivered run.
- `SOURCES.md`: source provenance, exact repository paths, and review limits.
- `PROOF_AUDIT.md`: theorem dependency and claim-boundary checklist.
- `build.sh`: verification plus three-pass PDF compilation into `build/`.
- `SHA256SUMS`: integrity hashes for the delivered files other than itself.

### Main results

Use U uniform on [-1/2,1/2], and mu_q the law of sum(q^k U_k, k >= 0).
The width of a uniform here is its full interval length.

For positive summable source widths s_k with s_k/s_l irrational whenever k != l,
a finite or countable convolution of uniforms of widths a_j divides the source
law exactly when a_j = s_(k_j)/n_j, with positive integers n_j and DISTINCT
source coordinates k_j. Equivalently, the Fourier quotient extends to an entire
function. A positive remainder is explicitly constructed by interval subdivision.

For q with no positive rational power this gives:

    dilation(c, mu_rho) divides mu_q
    exactly when c=q^a/n and rho=q^m/d,
    with a>=0, m>=1, and positive integers n,d.

Several geometric factors are compatible exactly when their source progressions
a_i + m_i*N are pairwise disjoint. The exact finite pairwise test is

    gcd(m_i, m_j) does not divide (a_i-a_j).

For q=p^(-e/h), p prime and gcd(e,h)=1, each proposed width has the unique
form q^r/n with 0<=r<h. Within each residue class the exact criterion is

    #{j: r_j=r and floor(v_p(n_j)/e)<=K} <= K+1 for every K>=0.

The h=1 Hall ingredient is PRIOR repository work and is explicitly credited.
The article proves the separated-width, geometric-stream, h-channel, and
finite-orbit extensions, as well as an explicit Wasserstein obstruction.

The uniform pair with widths 1/2 and 1/3 divides mu_(1/2), but does not divide
mu_q at any q with no rational positive power. Nevertheless its distance to the
factorable class tends to zero as such q approach 1/2; quantitative upper and
strictly positive lower bounds are proved.

### Proof and originality status

AI-assisted and unrefereed. The new analytic theorems have not been checked in
Lean, Rocq, or another proof assistant. The package is not a claim of certified
worldwide priority or a resolution of every convolution decomposition problem.
The classification concerns factors explicitly presented as sums of independent
uniforms, not arbitrary probability factors.

Existing multisection identities, the prime-power h=1 Hall theorem, the base-six
counterexample, and the golden-ratio Bernoulli singularity mechanism are credited
as prior or classical. All dependencies needed for the results are proved here.
The bibliography is contextual as well as historical; it does not substitute
for the proofs.

No repository files were modified and no pull request was created.

### Verification

Requires Python 3.10 or later. No third-party packages, network, or floating-point
arithmetic are required.

    python3 code/verify.py --output results/verification.rerun.json

The executed run passed 156,227 exact finite checks, including CRT comparisons,
Hall conditions versus independent backtracking, colored channels, geometric
orbit cases, exact moment identities, and deliberate invalid inputs.

These are implementation tests, NOT formal verification of the analytic or
infinite statements. The program accepts certified integer parameter forms;
it does not decide whether an arbitrary real parameter is nonresonant.

### Build

Use a TeX installation with pdfLaTeX, Latin Modern, AMS packages, mathtools,
microtype, booktabs, tabularx, enumitem, xcolor, fancyhdr, xurl, hyperref,
and cleveref. No bibliography processor or external figures are needed.

    bash build.sh

This creates `build/article.pdf` and `build/verification.json`, without replacing
the delivered PDF or verification receipt. Set `PYTHON` or `PDFLATEX` in the
environment to choose other executable names. Compilation timestamps may make
PDF bytes differ on rebuilding; they do not affect mathematical content.
