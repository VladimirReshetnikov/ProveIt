# Exact gaps for wide three-frequency progressions

The main note determines the supremal zero-free length for the spectrum
±{N,(m+1)N,(2m+1)N} for every positive integer N and integer m ≥ 2.
For odd m the same proof identifies the limiting polynomial and unique
six-point positive annihilator. See the note for the asymptotic and scope.

- three_frequency_gaps.tex / .pdf: proof and references.
- all_odd.js and cells.json: exact replay of the full cover of [0,1/3].
  Run `node all_odd.js`; no floating-point proposals are used in replay.
- guess.js: optional numerical proposal generator. Run
  `node all_odd.js --emit` to regenerate cells.json and then replay.
- limit.js: separate interval computation of the limiting constants.
- replay.txt: output of the full replay and the limiting computation.
- m3_cross_check/: earlier independent Chebyshev-polynomial solution for
  step 3N, with its own TeX/PDF and checkers.

No dependencies beyond Node.js for the main checks. Run pdflatex twice
to build the main PDF. Nothing in the result assumes RH or GRH.
