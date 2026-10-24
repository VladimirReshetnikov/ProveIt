# Diophantine consistency equations with powered saturation and factorial carriers

Round 14, 24 October 2026. Prepared for Vladimir Reshetnikov and ProveIt.

## Main results

- `norm/equation.json`: 12 unrestricted integer variables, exact degree 768, 141 live binary operations, using the unchanged six actual source34 coefficients. The 149-operation `equation_reduced.json` is the identical polynomial with cancellations explicit.
- `direct/integer519_centered`: one integer quartic, 519 variables, 321 squared quadratic residuals, 6253 collected terms, maximum absolute coefficient 411060.
- `direct/derived16_centered_shell`: one integer quartic, 517 variables, 310 residuals, 6774 terms, height 3904267.
- `architecture/derived16_cantor/natural`: one quartic over nonnegative integers, 349 variables, 268 residuals, 12768 terms, height 86915503.

The report gives all new unbounded arguments in TeX/PDF: powered-divisibility saturation; full supported-modulus Pell interpolation; reciprocal prime-power CRT; small amplification budgets; self-bounding factorials and noncircular digits; shared-factorial Horn flow; derived polynomial ranges; signed factorization, elimination, and translation.

These equations encode finite refutability. With the explicitly retained ordinary native and calculus calibration, ZFC proves that their unsolvability is equivalent to Con(ZFC). This is not a proof of consistency or a newly completed Lean/Rocq endpoint. Finite checkers do not establish the unbounded calibration. No global minimality or priority claim is made; a different retained native route already has a 37-integer quartic with enormous coefficients.

## Read first

The PDF at the archive root is the main report. Its complete editable source is `report/main.tex` and the adjacent TeX sections. `radicals/PROOF.md`, `norm/PROOF.md`, the three `architecture/*PROOF.md` files, and `direct/section.tex` retain the detailed branch records. `review/COUNTEREXAMPLE_SCOPE.md` distinguishes the rejected shared83/weakened86 interfaces from the unchanged source34 calibration.

## Replay offline

Requirements: Python 3.10 or later and SymPy. The direct, architecture, source coefficient, baseline, and polynomial checks otherwise use only the Python standard library. SymPy is not vendored; once installed, no network is used.

    python verify.py --report /tmp/round14-replay.json
    python -O verify.py --mode optimized --report /tmp/round14-replay-O.json

The first command runs normal and optimized children. The wrapper checks the complete release manifest and uses a fresh temporary copy for every mutating checker and generator. It rebuilds all three principal quartics and both norm graphs byte for byte, reconstructs source coefficient values, re-expands final and baseline polynomials, checks source projections and translations, and runs independent resultant and modular diagnostics. Original development paths are never executable dependencies.

The inherited coefficient recipe deliberately rejects optimized execution. The wrapper runs that one recipe normally in both modes, then explicitly compares its four outputs with the authentic payloads. All final correctness checks use explicit exceptions rather than disableable assertions.

Runtime dependencies imported by architecture generators retain their archive-relative directory hierarchy under `intake/`. Only needed code, data, proof texts, licenses, and literal baseline data are included; the original ZIPs are not. The source's Lean files document the retained interface but are not presented as a self-contained new Lean build.

## Equation formats

`norm/equation.json` is an integer arithmetic DAG. Leaves name one of twelve variables, a fixed integer, or one of the six coefficient ports. Internal nodes are binary add/subtract/multiply. `output` selects the polynomial; named registers do not create unknowns.

Each direct `equation.json` has an ordered `variables` list and a `residuals` list. Each term `[c,[i1,...,ik]]` means c times the product of the zero-based indexed variables. Repeated indices are powers and the empty index list is the constant monomial. The one equation is exactly the sum of squares of all residuals. The matching `expanded_polynomial.json` lists every collected nonzero coefficient.

## PDF build

With a normal TeX Live installation, repeat compilation until references stabilize (three passes are needed from a clean directory):

    cd report
    pdflatex -interaction=nonstopmode -halt-on-error main.tex
    pdflatex -interaction=nonstopmode -halt-on-error main.tex
    pdflatex -interaction=nonstopmode -halt-on-error main.tex

`verification/` records the actual replay and visual-review results. `MANIFEST_SHA256.json` hashes every shipped file other than itself. Reproducibility of polynomial artifacts is byte-exact; PDF bytes may vary with TeX versions and timestamps.

## Attribution

The public comparison pin is ProveIt 84e16e43092614bae262ca59651cb9d77e31a255. Named source pins, original notices, and licenses are preserved with their files. See `NOTICE.md`; inherited material keeps its own licenses. No external service, repository, or user account was modified to prepare this packet.
