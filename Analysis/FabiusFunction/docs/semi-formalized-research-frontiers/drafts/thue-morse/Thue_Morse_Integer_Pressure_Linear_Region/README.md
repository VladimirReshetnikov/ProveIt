# A Linear Positivity Region for Thue Morse Pressure

This bundle contains the seven-page report, editable LaTeX, reproducible exact checkers, and supporting data.

The theorem proves H_(m,m+s)>0 and positivity of the pressure coefficient at degree 4m+2s whenever m>=2048 and 128s+64<=m. This is a positive region of linear width beyond the first feedback boundary. The full proposed range below degree 6m remains open.

Three new estimates drive the proof: the sharp complete-multipartite matching multiplicity (d-1)_(2s+1), the exponential auxiliary-moment bound S_s<11(4*pi)^(2s), and contraction of the capped transfer operator on the fixed complex disk |a|<=1/16. All are proved in the report.

## Reproducing the checks

Run `python3 code/run_all.py` for the standard-library checks. These verify all 22 linear-strip side conditions, the rational saddle and tangent bounds, all 2,632 strengthened marked-pair profiles, and 35 saved true-response restoration identities.

Run `python3 code/reproduce_all.py` with SymPy installed to reconstruct the rational Fourier systems. It checks every original residual and normalization, recomputes the Schur data for m=2,...,8, and compares every deleted-insertion identity with the full nonlinear eigenvector recursion. These finite computations are supplementary identity checks; the universal linear-strip theorem follows from the analytic proof.

`make pdf` builds on a standard TeX installation. The optional `build_local.sh` creates a local format and uses the installed Debian TeX paths used during preparation. It does not install software or modify global configuration.

The `background` folder preserves the pinned original pressure source and the preceding mathematical reports. The earlier reports are dependencies and context, not silently revised copies. The new argument uses the pre-feedback triangle and the new offset-zero estimate, so it does not require replaying the earlier finite boundary enclosure archive.

The final PDF is `article.pdf`; its editable source is `article.tex`. Intermediate page images and TeX format files are excluded from the deliverable archive.
