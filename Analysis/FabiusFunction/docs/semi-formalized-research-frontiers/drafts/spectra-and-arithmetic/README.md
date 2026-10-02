# Spectra and arithmetic

## Source-only notation status (2026-09-01)

The two-adic-valuation notation pass changed the consolidated
`Spectra_and_Arithmetic_Frontiers` source and five standalone report sources.
The exact current live-TeX snapshots are:

| Live source | Lines | Bytes | SHA-256 |
|---|---:|---:|---|
| `Automatic_Scale_Factorizations_Rvachev_2026-08-30/automatic_scale_factorizations.tex` | 1,682 | 62,490 | `3e40fef5247ed3d7263ff885dc97159b456f26347614817fc18e087af647de90` |
| `Digital_Spectral_Geometry_and_Log_Periodic_Saddles/Fabius_Rvachev_Frontier_Report.tex` | 1,940 | 61,049 | `92d98914722f98b37f84a19283536c8b3925584d0729920b6346a4f572c735b1` |
| `Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors/Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors.tex` | 2,340 | 92,888 | checksum receipt retired (source amended editorially 2026-09-29 and 2026-09-30) |
| `fabius_holonomic_frontiers_report/fabius_holonomic_frontiers.tex` | 2,251 | 85,256 | `75f2a36ee0ae4b68e17030536cd7aa2cd922fea8941ed023afb272fafd29b20f` |
| `Fabius_Total_Positivity_Frontier_Report/Fabius_Total_Positivity_Frontier_Report.tex` | 1,060 | 58,362 | `e7f05ac66a92284e82886bfe8b3376715ca0f71493a217d5a1adab6c17171475` |
| `Spectra_and_Arithmetic_Frontiers/Spectra_and_Arithmetic_Frontiers.tex` | 8,183 | 349,076 | `683a560044772216980b05c4dd26957c6bbfb6c34019cc8d4cae815d9cff8df1` |

These metrics and hashes describe the live TeX only. No PDFs were regenerated
for that notation pass. Except for the later synchronized Dyadic Radon and
Carleman receipts stated explicitly below, every page-count, font,
visual-inspection, and three-pass-build statement remains evidence about its
earlier retained PDF checkpoint, not evidence of byte-level or rendered parity
with the current source. Package-local checksum ledgers are retired; their
prior checkpoint bytes, arrival provenance, and historical build hashes remain
recoverable from Git history and the package receipts.
`Fabius_Pascal_Frontiers_Report` likewise retains its already documented mixed
checkpoint: its reviewed PDF predates its current TeX.

## Direct-directory intake: late 2026-08-30 batch

Six tracked report directories arrived directly under `drafts/incoming/` in
`origin/main`, without ZIP archives or outer archive hashes.  They were moved
here in the quick intake phase and kept as separate manuscripts; the arrival
commits remain their byte-level provenance. Internal checksum ledgers were
verified against the submitted bytes, then refreshed only where Git's
repository policy had normalized CSV files from CRLF to LF; repository
ledgers were added where the delivery was incomplete. Those ledgers are now
retired and recoverable from Git history. All delivered PDFs in
this batch passed a structural `pdfinfo` read and were unencrypted; this was
not a visual review, experiment replay, TeX rebuild, mathematical audit, or
Lean verification.

- [`Automatic_Scale_Factorizations_Rvachev_2026-08-30/`](Automatic_Scale_Factorizations_Rvachev_2026-08-30/)
  contains *Automatic Scale Factorizations of the Rvachev Law* (retained
  22-A4-page PDF checkpoint; current live TeX: 1,682 lines, 62,490 bytes,
  SHA-256
  `3e40fef5247ed3d7263ff885dc97159b456f26347614817fc18e087af647de90`;
  with a 473-line program, eight data outputs, and three
  PDF/PNG figure pairs), from arrival commit
  `8a184546747082cbd92ad4675fb61981c6b8c3b6`. At its normalized intake
  checkpoint, the submitted ledger covered all 21 non-ledger payloads and
  verified after six CSV hashes were refreshed for LF storage and the JSON
  summary's missing final newline was repaired. The
  current source selects the retained PNG plot companions; the exact
  three-pass rebuild embedded and subset every font, retained Libertinus prose,
  and had no
  Type 3 fonts, while the vector-PDF plots remain reproducibility payloads. The
  corresponding exact three-pass render is a retained historical checkpoint,
  not a current source/PDF parity claim. No PDF was regenerated after the
  notation-only TeX change. The former ledger is retired and recoverable from
  Git history. Its
  Thue--Morse scale partition, q-Mahler, Mellin, moment, plateau, and endpoint
  themes remain standalone pending claim and experiment review, comparison,
  and a Lean crosswalk.

- [`Dyadic_Radon_Profiles_Fabius_Rvachev_2026-08-30/`](Dyadic_Radon_Profiles_Fabius_Rvachev_2026-08-30/)
  contains *Dyadic Radon Profiles in the Fabius--Rvachev Web* (at arrival: 31
  letter-paper pp and 2,064 source lines; with a 624-line program, ten data
  files, and four PDF/PNG figure pairs), from
  `03b2f61889674f7d64ac86d3233236f5fa7ce660`. Its former complete 26-entry
  ledger recorded the repository-normalized bytes; nine CSV entries changed
  only by CRLF-to-LF normalization. The ledger is now retired and recoverable
  from Git history. The title and abstract concern spectral
  reconstruction of dyadic projection profiles, zero multiplicities,
  q-sampled cumulants, automatic signs, Pascal factorizations, and exact
  cubature. The current 2,050-line, 74,839-byte source has SHA-256
  `0ac7695620cb22896bb912598e2e91fd404e70dbd3c5d1e769ee76a6e92578d4`.
  Three serial halt-on-error passes from absent auxiliaries produced
  27 pages/984,841 bytes, 29 pages/998,017 bytes, and a final 29-page,
  998,017-byte PDF with SHA-256
  `39e76001f71c6628308ccdb8232251538674faee3c9102fa26e4cec00eb276c0`.
  The final log, metadata, A4/rotation-zero, all-page render/text, and
  representative visual gates passed; all 24 font rows are embedded/subset,
  six are Libertinus, none is Type 3, and generated sidecars are absent.

- [`Fabius_Pascal_Frontiers_Report/`](Fabius_Pascal_Frontiers_Report/)
  contains *Automatic Spectra, Exact Dyadic Cubature, and Probabilistic Duals
  in the Pascal--Rvachev Hierarchy* (26 A4 pp, 1,927 source lines; with a
  426-line program, four CSV tables, and a captured numerical summary), from
  `8a184546747082cbd92ad4675fb61981c6b8c3b6`. The nine-file delivery had no
  checksum ledger or dependency lock. A repository-generated ledger formerly
  recorded the nine-payload scope; it is now retired and recoverable from Git
  history. The retained 26-page A4 PDF was
  rebuilt in exactly three serial passes and has complete metadata,
  embedded/subset Type 1 fonts, six Libertinus rows, and no Type 3 font. The
  source changed after that receipt, so a new build is required before
  synchronization is claimed. The former ledger recorded that exact mixed
  checkpoint and is now retired and recoverable from Git history. Its higher-rank spectral
  signs and Lambert series, dyadic cubature, Laguerre--Pólya/Pascal hierarchy,
  and probabilistic duals remain pending comparison.

- [`fabius_holonomic_frontiers_report/`](fabius_holonomic_frontiers_report/)
  contains *Holonomic Rank, Exact Overlaps, and Non-P-Recursiveness in the
  Fabius--Rvachev System* (retained 30-A4-page PDF checkpoint; current live
  TeX: 2,251 lines, 85,256 bytes, SHA-256
  `75f2a36ee0ae4b68e17030536cd7aa2cd922fea8941ed023afb272fafd29b20f`;
  with a 644-line
  experiment, six CSV tables, a generated TeX fragment, a captured text
  check, and five PDF/PNG figure pairs), from
  `6d6737530ec541196c506f95ec20a701a29872b3`. Six CSV hashes in its complete
  26-entry ledger were refreshed for LF storage. At intake, all six delivered
  PDFs were readable and unencrypted (35 pages total). Those retained PDFs
  predate the current notation-only TeX; no PDF was regenerated, and the
  former checksum ledger is retired and recoverable from Git history. The
  report concerns finite
  sinc-product differential rank, exact signed overlaps, dyadic
  Thue--Morse/frequency spectra, and non-D-finiteness/non-P-recursiveness.

- [`Fabius_Rvachev_Carleman_Frontiers_2026-08-30/`](Fabius_Rvachev_Carleman_Frontiers_2026-08-30/)
  contains *Critical Ultradifferentiable Geometry of the Fabius--Rvachev
  System* (at arrival: 24 A4 pp and 1,941 source lines; with a 544-line program,
  four CSV tables, and five PDF/PNG figure pairs), from
  `92c9909242ed6a2ab51d68ed816d1aa2a5339719`. Four CSV hashes in its complete
  21-entry ledger were refreshed for LF storage. Its derivative spectrum,
  Denjoy--Carleman scales, discrete Fourier duality, lattice corrections,
  Lambert-W saddles, and Bell-edge behavior remain pending comparison and
  formalization. The current 1,934-line, 71,224-byte source has SHA-256
  `49dd91c71df292725e9dfe6de450ac014b47f3c3ba4a5bc8ec02e2d2e76d34e3`.
  Three serial halt-on-error passes from absent auxiliaries produced
  24 pages/952,942 bytes, 24 pages/973,424 bytes, and a final 24-page,
  973,424-byte PDF with SHA-256
  `13a7f35e23dc5a794d46b431059ce35c0b48c199f1996539b65dee9bc8c16047`.
  The final log, metadata, A4/rotation-zero, all-page render/text, and
  representative visual gates passed; all 22 font rows are embedded/subset,
  four are Libertinus, none is Type 3, and generated sidecars are absent.

- [`Dyadic_Spectral_Divisors_and_Gamma_Duality/`](Dyadic_Spectral_Divisors_and_Gamma_Duality/)
  is the title-derived filing of the generic incoming wrapper
  `Fabius_Rvachev_Frontier_Report-F/` from
  `d4605275f58f648ebcdeb74bc2ef5e4983abb6f0`. *Dyadic Spectral Divisors and
  Gamma Duality* is 22 A4 pages and 1,301 source lines, with a 379-line
  program, seven generated outputs, and three PDF/PNG figure pairs. Its
  submitted 3-entry ledger verified those three payloads but was incomplete;
  a repository-added full arrival ledger recorded all 20 delivered files,
  including the submitted ledger. Both are now retired and recoverable from
  Git history. Its dyadic zero divisor,
  Laguerre--Pólya/non-holonomic structure, reciprocal-base counting, heat
  traces, Gamma/Thorin duality, and Lambert inversion remain separate pending
  semantic deduplication and a Lean crosswalk.

These reports overlap one another and the consolidated spectra volume in
zero-divisor arithmetic, Pascal/valuation profiles, derivative growth,
Laguerre--Polya and Pólya-frequency structure, holonomicity, and
non-P-recursiveness.  That claim-level comparison is intentionally deferred
until after publication.  A theorem label, proof in prose, symbolic
calculation, or numerical check in any manuscript does not imply that the
claim has been proved in Lean.

New standalone intake member:
[`Digital_Spectral_Geometry_and_Log_Periodic_Saddles/`](Digital_Spectral_Geometry_and_Log_Periodic_Saddles/),
*Digital Spectral Geometry and Log-Periodic Saddles* (retained 24-A4-page PDF
checkpoint; current live TeX: 1,940 lines, 61,049 bytes, SHA-256
`92d98914722f98b37f84a19283536c8b3925584d0729920b6346a4f572c735b1`),
arrived from the
rootless `Fabius_Rvachev_Frontier_Report_Package.zip` on 2026-08-30. The
title-based directory avoids collision with an unrelated q-series package
that used the same generic report filename. Its delivered zero-file audit was
replaced by a reproducible recursive audit of 188 prior TeX files (390,119
lines and 16,813,357 bytes) excluding this package directory, with raw corpus
digest `bb8a7de4c16a960f8d640d99797085b4f17cd0cdcc38b38caa4014536806b4d3`.
Its
failed numerical generation was repaired and rerun at 80-digit precision,
producing all three optional figures and the generated tables. No theorem-
level novelty is accepted on intake: the divisor/zeta/count/heat/cumulant,
exact `K`/Lambert/base-family, Appell/first-defect, Legendre--Bessel, sub-
Gaussian, and endpoint/inverse strands all have exact or stronger prior homes
in the consolidated corpus. Only minor corollary-level residue remains to
assess. The all-orders saddle and inverse claims were downgraded for a missing
uniform remainder, the global Strang--Fix conclusion was restricted to the
proved canonical Appell defect, and the false strict-curvature range was
corrected using center flatness at `b=2` and the exact plateau for `b>2`.
The report remains a separate overlap intake; its labels assert neither
novelty nor Lean status. It now reproduces the current primary document's
canonical A4 package, theorem, macro, boxed-environment, and listing-style
block verbatim, apart from permitted metadata and running-head text, with only
four required local notation commands appended. At its render checkpoint, the
validated PDF used fully embedded, subset Libertinus fonts and no Type 3 fonts,
and the then-current payload checksums, including the ten-entry arrival
ledger, passed completely (18/18). Those ledgers are now retired and
recoverable from Git history. That retained PDF predates the current
notation-only TeX; no PDF was regenerated.

New standalone intake member:
[`Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors/`](Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors/),
*Reciprocal-Integer Convolution Divisors of the Rvachev Law* (retained
35-A4-page PDF checkpoint; current live TeX: 2,340 lines, 92,888 bytes
(amended editorially 2026-09-29 and 2026-09-30; checksum receipt retired);
with a 352-line exact/numerical experiment),
arrived from a rootless 14-file archive on 2026-08-30.  The package's
characteristic quotients
`Q_M(z) = Phi(z) / Phi(z/M)` classify reciprocal-integer decompositions of
the Rvachev law.  Its digit IFS and multiplicative cocycle lead to an exact
odd-singular/even-regular trichotomy, transport and inverse-Fabius bounds,
an arithmetic zero divisor and spectral zeta function, and finite
Thue--Morse quotients whose `M = 3` case recovers Stern/hyperbinary
coefficients.

This is a distinct sibling of the shape/Stein report under
[`../representations/`](../representations/): unequal reciprocal-scale
factors here do not conflict with that report's obstruction to identical
convolution roots.  The report nevertheless shares foundational zero-count,
Bernoulli/Bell, endpoint, and inverse-Fabius infrastructure with the
consolidated corpus, so it remains separate pending a theorem-by-theorem
crosswalk. The rootless archive supplied no checksum ledger or dependency
lock; at the repaired package checkpoint, the repository-generated 14-entry
`SHA256SUMS` covered every stored payload after five CSV files were normalized
to LF. The repair gives the
report a title-derived source/PDF pair and canonical A4/27 mm/Libertinus
styling; three final `pdflatex` passes produced the retained 35-page PDF with
all fonts embedded and subset, no Type 3 font, and no overfull box. Key pages and every
figure were inspected at that checkpoint. The PDF predates the current
notation-only TeX; no PDF was regenerated, no current source/PDF parity is
claimed. The former checksum ledger is retired and recoverable from Git
history. A temp-isolated
Python 3.12 replay regenerated every output: four
CSVs were byte-identical, the text summary was EOL-equivalent, and the endpoint
CSV had only 66 last-place differences (maximum `1.11e-16`).  All four PNGs
showed the expected layout drift between the unpinned packaged Matplotlib
3.10.8 and replayed 3.11.1 (1475 versus 1476 pixels wide), strengthening the
case for a dependency lock. The report cites the adjacent exact
`GeneralizedZeroDivisor` and `ReciprocalIntegerGammaZeros` APIs without
claiming that the quotient-family results themselves are formalized.
Manuscript theorem labels do not imply Lean proof status.

Archival arrival of 2026-09-28:
[`Arithmetic_Convolution_Factors_Fabius_Type_Laws/`](Arithmetic_Convolution_Factors_Fabius_Type_Laws/),
*Arithmetic Convolution Factors of Fabius-Type Laws* (26-page A4 PDF,
1,813-line source, an exact standard-library regression program), filed by
a quick archival intake from the repository-level `docs/incoming/` drop
zone.  It classifies scaled convolution factorizations
`μ_A = D_c μ_B * ν` of laws of `Σ_k U_k/A_k` along divisibility ladders:
they exist exactly when `c = 1/m` and `A_k ∣ m B_k`.  Its dyadic single-law
case is the reciprocal-integer scale classification of
`Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors/`, and its base-2
remainder regularity matches that report's parity classification; the
article does not cite that report, so the overlap is recorded here for the
deferred comparison.  Its new layers are the two-ladder criterion, the
encoding of inclusion modulo finite sets with a no-Borel-invariant theorem,
arithmetical-hierarchy completeness results, and Wasserstein bounds.
Its self-spectrum theorem, stated for every real ratio, already proves
item 1 of the reciprocal-integer report's `conj:general-base` for every
integer base (that report now carries a note of 2026-09-30 saying so).
Editorial notes of 2026-09-30 point its questions "Beyond divisibility
ladders", "Two arbitrary geometric ratios" and "Optimal approximate
factorization" to the off-resonance article below.
Unreviewed; no Lean statement.

Archival arrival of 2026-09-29:
[`Simultaneous_Convolution_Divisors_Fabius_Type_Laws/`](Simultaneous_Convolution_Divisors_Fabius_Type_Laws/),
*Simultaneous Convolution Divisors of Fabius-Type Laws* (24-page A4 PDF,
1,671-line source, an exact standard-library certificate program), filed
by a quick archival intake from the repository-level `docs/incoming/`
drop zone.  It decides which families of uniform laws can be removed
*together* from the prime-base law `X_p = Σ p^{−k}U_k`: exactly the
reciprocal-integer widths `1/n_j` with `#{j : v_p(n_j) ≤ K} ≤ K+1` for
every `K`, a Hall matching condition equivalent to entire extensibility
of the Fourier quotient.  It adds finite certificates for geometric
streams, prime-power targets, coordinate rigidity in several dimensions,
and a regularity classification of the residual; a base-six quotient
shows that zero cancellation does not imply positivity for composite
bases.  Its one-stream cases are theorems of the two reports above, and
it recovers the reciprocal-integer report's single-copy theorem; it does
not cite the arithmetic-factor report, whose question "Beyond
divisibility ladders" it answers for prime-power geometric targets.  The
finite part of its base-six quotient (caps `h`, `6h` over `2h`, `3h`,
quotient `1 − u + u²`) reappears, uncited, in two observation-mask notes
of `../representations/` (batch 72), which show that nine further
uniforms of length `h` make it positive; an editorial note of 2026-10-01
records this.  Unreviewed; no Lean statement.

Archival arrival of 2026-09-30:
[`Arithmetic_Rigidity_off_Resonance_Geometric_Uniform_Laws/`](Arithmetic_Rigidity_off_Resonance_Geometric_Uniform_Laws/),
*Arithmetic Rigidity off Resonance* (25-page US Letter PDF, 949-line
source, an exact standard-library certificate program), filed by a
quick archival intake from the repository-level `docs/incoming/` drop
zone and amended editorially the same day and on 2026-10-01 (its README
lists the amendments).  It takes the convolution-factor problem of the two articles
above off integer ratios: when the source widths are pairwise
rationally incommensurable, a family of uniforms divides the law
exactly when its Fourier quotient is entire, exactly when each uniform
refines its own source coordinate by an integer.  So for every `q`
with no rational positive power, `D_cμ_ρ` divides `μ_q` exactly when
`c = q^a/n` and `ρ = q^m/d`, and several geometric factors divide
together exactly when their source progressions are disjoint; at
`q = p^{−e/h}` the problem splits into `h` prime-adic Hall problems,
with a finite-orbit criterion for one geometric factor.  It answers the
arithmetic-factor article's question "Two arbitrary geometric ratios"
for all but countably many target ratios, credits the simultaneous
article's prime-power Hall theorem and base-six example, and re-proves,
uncited, the arithmetic-factor article's self-spectrum theorem and uses
the mechanism of its Wasserstein bound (editorial notes now record both,
with reciprocal notes in the arithmetic-factor, simultaneous and
reciprocal-integer articles); it adds
a Wasserstein separation bound and a family near `q = 1/2` on which
exact factorability fails while the distance to it tends to zero.  For
observation masks of one geometric family its separated-width theorem is
re-proved, uncited, by
`../representations/Arithmetic_Geometric_Mask_Order/` (mask inclusion
when no power of `q` is rational), and two other notes of that series
carry out the finite Laurent-polynomial step of its question "Composite
reciprocal returns" for finite sources; editorial notes of 2026-10-01
record both.  Unreviewed; no Lean statement.

Archival arrival of 2026-10-01:
[`Wasserstein_Contact_Orders_Uniform_Factor_Resonances/`](Wasserstein_Contact_Orders_Uniform_Factor_Resonances/),
*Wasserstein Contact Orders at Uniform Factor Resonances* (17-page US
Letter PDF, 737-line source, five finite checkers with receipts), filed
by a quick archival intake from the repository-level `docs/incoming/`
drop zone (its revision 2; the first edition was not filed).  It answers
the question "Sharp distance to a resonance" of the article above: for
the factor `U_{1/2}*U_{1/3}` the Wasserstein distance from `μ_q` to the
laws with that factor is of exact first order at `q = 1/2`, with
one-sided coefficients between `|P|/(6π(1+12π))` and `1/4` described
by an `L^1` tangent cone, and at most `|q − 1/2|/4` everywhere, so the
leading perturbation cannot be cancelled.  For the factor
`U_{1/B}*U_{B^{−j}}` the distance has exact order `|q − 1/B|^j` from
both sides, for every fixed integer base `B ≥ 2` and depth `j ≥ 1`:
every positive integer contact order occurs.  The lower bounds compare
Fourier derivatives at a double zero; the upper bounds construct
genuine probability remainders.  It credits the arithmetic-factor
article's `prop:wasserstein` and the article above.  Unreviewed; no
Lean statement.

[`Fabius_Total_Positivity_Frontier_Report/`](Fabius_Total_Positivity_Frontier_Report/),
*Total Positivity and Cartwright Geometry in the Fabius--Rvachev Dyadic Sinc
Product* (retained 24-page PDF checkpoint; current live TeX: 1,060 lines,
58,362 bytes, SHA-256
`e7f05ac66a92284e82886bfe8b3376715ca0f71493a217d5a1adab6c17171475`),
arrived as a bare TeX/PDF/script package on 2026-08-30.
Its imaginary-square-root transform, Laguerre--Polya and multiplier-sequence
structure, exact zero divisor and Thue--Morse sign interpolation, Cartwright
geometry, and geometric-scale deformation extend the arithmetic/spectral
Fourier-product theme. The package shipped no checksum ledger, README,
environment pin, or captured run output. The repository repair regenerated
the four required figure/table inputs and four CSV evidence tables, normalized
the source to A4/Libertinus, rebuilt the PDF in three passes, and added a
12-entry payload ledger for that checkpoint; exact arrival hashes remain
recorded in the global manifest. The former ledger is now retired and
recoverable from Git history. That retained PDF predates the current
notation-only TeX; no PDF was regenerated and no current source/PDF parity is
claimed. The current source crosswalks the exact finite
general-base digit
count in `BaseDigitMultiplicity.lean` without promoting the analytic zero or
sign claims. Its novelty screen is already stale at its pinned
snapshot: matching Laguerre--Polya/PF-infinity/shifted-Jensen and zero-sign
material appears in `Frontier_Compilations/`. It therefore remains standalone
pending claim-by-claim crosswalk and deliberate deduplication. Its paper
theorem labels do not by themselves assert Lean status.

Arithmetic and spectral structure of the Rvachev Fourier product,
consolidated (2026-08-28) into the single volume
[`Spectra_and_Arithmetic_Frontiers/`](Spectra_and_Arithmetic_Frontiers/).
Its current live TeX has 8,183 lines and 349,076 bytes, with SHA-256
`683a560044772216980b05c4dd26957c6bbfb6c34019cc8d4cae815d9cff8df1`.
The retained PDF was not regenerated after the notation-only source change,
so its earlier render validation is a historical checkpoint rather than a
current source/PDF parity claim. The former checksum ledger is retired and
recoverable from Git history.
The consolidated volume comprises:

- **Part I** — *Half-Integer Spectral Arithmetic*
  (formerly `Fabius_Half_Integer_Spectral_Frontier_Report/`);
- **Part II** — *Arithmetic Dyadic Rays of the Rvachev Fourier Product*
  (formerly `Fabius_Arithmetic_Rays_Frontier_Report/`);
- **Part III** — *Spectral Arithmetic and the Pascal–Rvachev Hierarchy*
  (formerly `Spectral_Arithmetic_Pascal_Rvachev_Hierarchy/`);
- **Part IV** — *Derivative Norm Spectra and Dual Moment Geometries of
  the Fabius–Rvachev System*
  (formerly `Fabius_Derivative_Norm_Spectrum_bundle/`, whose data,
  figures, and scripts live under `assets/`).

The member drafts were absorbed verbatim (labels, citation keys, and
asset paths mechanically prefixed per part; no mathematical content
altered) and their directories deleted; provenance with SHA-256 hashes
is recorded in the volume itself, and git history is the archive.

See [`../MANIFEST.md`](../MANIFEST.md) for titles and the previous paths.
