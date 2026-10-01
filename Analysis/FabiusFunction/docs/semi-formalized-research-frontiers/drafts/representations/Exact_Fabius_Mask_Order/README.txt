EXACT OBSERVATION ORDER FOR FABIUS CONDITIONING
1 October 2026

Result
For common exponentially tilted uniform coordinates with divisible caps, an earlier observation mask deterministically reproduces a later coordinatewise mask by taking residues modulo the later caps. The same map works under every integrable total-sum reweighting. This gives exact finite-parameter Blackwell and convex-divergence comparisons, including overlapping masks and countably many observations.

The report constructs a unique weakly continuous exact-sum conditional law on every interior sum value and proves the same comparison there. Equality is treated separately; nonconstant periodic reweightings can give equality. In the reciprocal-integer Fabius model with the standard phase convention, the earlier-versus-later prefix overlap ordering is strict for every n>=3 and 1<=m<n (in the phase cell 1<=rho<M of Corollary 4.1; a later note of the series makes it strict for every ratio q, every rho>0 and n>=2, see the editorial amendments below).

Scope
The cap divisibility assumption is essential to the exhibited residue map. This is not a theorem for all cap ratios or a complete sharp-rate classification of arbitrary observation masks. Exact-conditioning endpoints are not prescribed. The equality characterization for likelihoods is for dominated reweightings; full-configuration exact conditioning may be singular. Classical integer/fractional exponential independence and Blackwell comparison principles are explicitly credited. The proof is ordinary mathematics, not externally refereed or Lean formalized.

Contents
- exact_fabius_mask_order.pdf: research report (eight pages since the editorial amendments below; seven as delivered)
- exact_fabius_mask_order.tex: complete editable proof source
- SOURCES.txt: pinned repository source and primary literature
- checks/: standard-library exact regression programs, results and logs
- validation.json: mathematical verification scope and PDF quality record
- SHA256SUMS: checksums (retired on filing; not in the repository)

Verification
Run python3 checks/run_all.py. No third-party Python packages are required. (Since the editorial amendments below it writes its JSON and logs to checks/rerun/ unless --output-dir is given; on the ProveIt machine use py.)
The grid checker verifies 6,144 involutions, 205 mask comparisons, 41 nonconstant periodic-equality cases, 1,107 exact-total mask identities, and 30 common-observation identities. The separate continuous slice checker proves 775 rational moment identities, including internal sum breakpoints, and checks a strict total-variation example exactly. These finite checks test accounting and formulas; the universal continuous proof is in the report.

PDF build
Run bash build.sh with a standard TeX Live installation providing pdfLaTeX, Latin Modern, AMS packages, geometry, microtype, hyperref, xurl and booktabs. Three passes resolve references. (build.sh builds in build/ and then copies the PDF over the filed one; build on a copy.)

Editorial amendments (ProveIt, 2026-10-01)
------------------------------------------
Made in the editorial pass after batch 72 of docs/incoming/ (see
docs/incoming/README.md); every change to the source is marked
"% ed. (2026-10-01)", every change to a program "ed. (2026-10-01)". The
mathematical text is unchanged. The pdfauthor entry and byline ("Research
note prepared for Vladimir Reshetnikov with OpenAI") are kept as delivered.
This is the first of eight notes of one series, filed beside one another in
the order written: ../Exact_Fabius_Mask_Order/,
../Universal_Garbling_Classification/, ../Universal_Fabius_Mask_Criterion/,
../Uniform_Smoothing_Mask_Stabilization/, ../Arithmetic_Geometric_Mask_Order/,
../Exact_Fixed_Conditioning_Order/, ../Strict_Fabius_Conditioning_Order/,
../Proportional_Fabius_Mask_Edgeworth/.

- exact_fabius_mask_order.tex: an unnumbered environment ednote ("Editorial
  note (ProveIt, 2026-10-01)") is defined after the theorem environments (no
  counter changes). Two notes:
  - after the remark that ends Section 4: (12) holds for every q in (0,1),
    with all f-divergences, by Corollary 4.1 of
    ../Exact_Fixed_Conditioning_Order/ (with a kernel that may depend on the
    conditioning; a kernel common to all total-sum weights exists for other
    ratios only under Theorem 2.1 of ../Arithmetic_Geometric_Mask_Order/);
    Corollary 4.1 here is contained in Corollary 4.2 of
    ../Strict_Fabius_Conditioning_Order/ (strict for every q, rho > 0,
    n >= 2 and 1 <= m < n), which also makes the strict order of the
    second-order article, called eventual in this section, hold at every
    finite n; Proposition 3.1 also gives strictness for strictly convex
    divergences of finite value in its phase cell, which the later note does
    not assert;
  - after Question 3, a series map: the eight notes in the order written;
    the "separate companion research note" [4] is
    ../Second_Order_Critical_Complements_Fabius_Conditioning/ (batch 71,
    filed before the commit pinned here), and [3] is
    ../Critical_Complements_Sharp_Information_Loss/; the later notes that
    re-prove the sufficiency of Theorem 1.1 (for geometric caps only); and
    the partial answers to Questions 1-3 (Theorem 1.1 of the second note and
    the Gaussian-polynomial comparisons of the third; Theorem 1.1 of the
    seventh; Corollary 5.1 of the eighth).
- exact_fabius_mask_order.pdf: rebuilt from the amended source with
  three pdflatex passes (MiKTeX 26.2, pdfTeX 1.40.29), on a copy:
  8 A4 pages (7 as delivered), 369,307 bytes; all 19 fonts embedded, none
  Type 3; the final log has no error, overfull or underfull box, undefined
  or multiply defined reference, duplicate destination, or rerun request.
  The pages carrying the notes were rendered and inspected.
- checks/run_all.py, checks/verify_modulo.py, checks/check_slices.py: new
  option --output-dir (default checks/rerun/), which receives
  verification.json, slice_checks.json and the two console logs
  verify_modulo.log and check_slices.log, written with LF line endings. As
  delivered, the checkers overwrote the recorded JSON beside themselves and
  run_all.py the recorded logs, with CRLF line endings on Windows. Pass
  --output-dir checks (from this directory), on a copy, to regenerate the
  recorded files. A rerun of the amended run_all.py on a copy (2026-10-01,
  py checks/run_all.py, Python 3.14.4, standard library) passed and wrote all
  four files equal to the recorded ones byte for byte.
- build.sh: kept as delivered (see "PDF build" above).
- validation.json: pdf_pages set to 8; its other entries are as delivered.
- README.txt: the page count and the retired ledger under "Contents", the
  parentheses under "Result", "Verification" and "PDF build", and this
  section.
