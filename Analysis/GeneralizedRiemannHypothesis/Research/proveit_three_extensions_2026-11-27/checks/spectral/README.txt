FOUR WIDE ARITHMETIC FREQUENCIES

Scope
-----
This research extension determines the exact largest zero-free interval for
the spectrum +/-{N,(m+1)N,(2m+1)N,(3m+1)N}, for every positive integer N and
integer m >= 2. The new part is the nonresonant family of odd m >= 3. The
even-m case follows from the common sign change under half a period.

This is an unconditional infinite family of cases of Question 1 in:
Gady Kozma and Ferenc Oravecz, On the gaps between zeros of trigonometric
polynomials, Real Analysis Exchange 28 (2002/03), 447-454.
https://arxiv.org/html/math/0601021v1

It does not resolve Question 1 for arbitrary progressions, and the new
research proof is not a Lean or Rocq formalization.

Repository comparison
---------------------
Pinned ProveIt commit: 42efb893353a150857f5c8e2f9e7732d0d46f15f
The merged Article/sections/fil.tex gives two-frequency optima and general
large-K wide-step asymptotics. The current incoming report
kozma_oravecz_three_frequency_2026-11-28 gives all three-frequency
integer-ratio cases. The incoming positive-fourier-zeros/kozma/gaps.tex
gives a finite algebraic rule for general three-frequency progressions,
and explicitly asks what happens with four or more frequencies.
The four-frequency result here was not found in the inspected current
article or incoming reports. A targeted primary-source web search did not
locate a prior publication of this family. That search is not a guarantee
of publication priority.

Exact proof replay (Python standard library only)
------------------------------------------------
Run these commands from the directory containing this README:

  python3 -S four_frequency_certificate.py replay
  python3 -S verify_four_frequency_values.py
  python3 -S verify_m3_polynomial.py

Do not pass -O; checks require assertions and the program rejects that flag.
The first command checks 1127 rational parameter cells covering [0,1/3].
It uses only exact integer interval arithmetic, with rigorous rational
Taylor remainder bounds. All root proposals and preconditioners are read
as exact decimal rationals from four_frequency_cells.json. No root finder
is imported during replay. Global positivity, all dual weights, and the
odd-mode determinant are checked throughout every parameter cell.

The second command independently certifies isolated point roots, decimal
gap enclosures and the first two asymptotic coefficients, using the
separate four_frequency_point_witnesses.json.

The third command checks the m=3 member in the different coordinate
y=cos(theta), with integer Chebyshev polynomials. It uses no trigonometric
evaluation or continuum witness. It verifies global positivity on 3308
interval boxes, the positive dual measure and its uniqueness determinant.

Generation and figures
----------------------
NumPy and SciPy are needed only to regenerate proposed continuum cells:

  python3 four_frequency_certificate.py generate

The regenerate command still accepts a cell only after exact verification.
NumPy and Matplotlib are needed for the optional illustration:

  python3 plot_four_frequency.py

The plotted case uses frequencies 1,4,7,10. Its critical polynomial is
nonnegative and has six interior touching zeros plus its two endpoint
zeros. Perturbed polynomials are strictly positive on intervals approaching
the critical length; the maximum zero-free length is not attained.

Manuscript and data
-------------------
../../sections/four_frequencies.tex: theorem, complete analytic reduction and proof.
four_frequency_cells.json: exact rational continuum witness.
four_frequency_point_witnesses.json: isolated root and derivative proposals.
m3_polynomial_witness.json: separate algebraic witness for the m=3 case.
../../validation/continuum_replay.log: fresh standard-library-only replay.
point_verification.json: certified decimal intervals.
m3_polynomial_verification.json: independent polynomial cross-check.
../../figures/four_frequency_m3.pdf, .svg, .png: illustrative figure.
m3_illustration_data.json: non-proof numerical coefficients, nodes, masses.

Main certified example
----------------------
0.63147839169477181 < M({1,4,7,10}) < 0.63147839169477182.
The exact value is specified by the unique analytic contact system, not by
its displayed decimal approximation.
