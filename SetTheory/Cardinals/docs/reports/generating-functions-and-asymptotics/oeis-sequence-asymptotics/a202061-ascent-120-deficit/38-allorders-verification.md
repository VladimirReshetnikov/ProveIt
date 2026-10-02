# Verification and scope

The integrated 20-page report is reviewed against the exact source notes and
pinned positive-kernel dependency. Its analytic claims hold at every fixed
inverse-log order, subject to those imported enumerative/analytic inputs.
They do not give a multiplicative coefficient equivalent, a power prefactor,
growing-order uniformity, or an exact inverse rounding rule.

## Mathematical checks

`bash verify_all.sh` passes. The full transcript is `producer-replay.txt`.
The exact checks comprise:

- Universal peak-k recurrence through global P4, with degree and leading terms
- Separate original-duration/action substitution through P2
- Independent original-duration/action substitution through P4, using fresh
  local row coefficients and Gamma-jet beta moments
- Exact bounded-shift inverse identities and polynomial covariance through P4
- Symbolic K-dependent error exponents in the reduction ledger
- Independent local p1, p2, p3 cancellation
- Four direct convergent beta-log quadratures at 65-digit working precision
- Unexpanded fixed-core action checks at T=100,200,400,800
- Exact source hashes and all inherited mathematical checks

The P3/P4 portable verifier changes only how two source hashes are located.
`checks/check_proof_sources.py` compares it against its original and rejects
any mathematical change. Verification does not require the original research
workspace. The diagnostic quadrature has alpha=v=1, c=0, b=exp(20), and k_N
through p3; it is not a computation of sequence coefficients.

## Dependency integrity

Every payload file of the approved third-order report is copied unchanged,
including its nested reports and their manifests. The pinned top-level
third-order manifest has SHA256
46235c0b3313375922cd4f0663e1e3bbb470a25384b9841caa5e827e691167a0.
The exact file set and all 120 hashes in that manifest are verified.

## PDF and release checks

The article builds with three pdfLaTeX passes and no overfull boxes or
unresolved references/citations. All 20 final pages were rendered and visually
inspected; a second complete inspection agrees. The PDF and all five TeX
sources are bound to the independent integrated review by their hashes.

A fresh extraction is used to rerun the complete verification chain and rebuild
the PDF. In the tested toolchain, the rebuilt PDF matches byte for byte, the
payload manifest remains valid after rebuilding, and regenerating the ZIP
reproduces identical archive bytes. The final archive is checked again after
packaging. Build caches and page PNGs are excluded from the released payload.
