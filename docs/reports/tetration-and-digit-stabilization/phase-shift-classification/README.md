# Phase-shift classification for integer tetration

Prepared for Vladimir Reshetnikov, 19 September 2026.

The article gives an elementary proof of the 21-word phase-shift conjecture
in OEIS A376842, using the documented height-one speed convention. It also
proves the 14-word even-base restriction from the appendix of Marco Ripà's
2025 paper, and the 28-word prescribed-anchor conjecture in OEIS A376446.
This is a research draft: the arguments have not undergone independent peer
review or formal proof-assistant verification. A targeted literature check
found the conjectures still explicitly stated, but does not establish priority.

## Read first

- `tetration_phase_classification.pdf`: complete article, proofs and references.
- `tetration_phase_classification.tex`: complete editable source.
- `SOURCE_STATUS.md`: source versions, definition conventions and data audit.

The main structural result compares the 2-adic and 5-adic valuations of
D_b = T_(b+1) - T_b. At the first permanently constant-speed height, these
valuations are either strictly ordered or identically balanced. Strict
2-adic dominance gives the constant phase 5; strict 5-adic dominance gives
a multiplicative orbit in F_5^*; balanced valuations give exactly four
additional anchored words. The proof includes the first-height anchoring
step, not merely eventual periodicity.

## Reproduce the computations

Python 3.9+ and the standard library are sufficient. The saved run used
Python 3.13.5. Compatibility was not tested separately on every version.
From the extracted directory:

```text
python code/phase_tetration.py 57
python code/phase_tetration.py 901
python code/verify.py --max-base 100000
```

Do not use Python's `-O` option: it disables the assertions used by the
verification program. To preserve the bundled results, direct a new run to
another directory:

```text
python code/verify.py --max-base 100000 --output rerun-data
```

A faster run is `--max-base 1000`. The minimum is 901, so all required
small witnesses remain in range. The default independent random sample has
100 cases with a fixed seed, plus seven structured cases. Use
`--random-cases N` to change the random sample size. The tests also check
small towers constructed as full integers, including T_5 for base 2.

The saved full run checked:

- 89,999 admissible bases from 2 through 100,000, excluding multiples of 10;
- 719,992 post-onset phase positions;
- 3,006 direct-integer residue, capped-tower and valuation checks;
- 107 comparisons against a second full-modulus Euler-lifting algorithm;
- seven structured sharp-onset examples, up to onset 34 and 1,055 stable digits.

All mathematical assertions passed. The audit deliberately records the one
mismatch with the accessed OEIS values: at base 21, the listed word is 6248,
whereas the documented convention and exact calculation give 2486. This is
a rotation/anchor discrepancy, not a counterexample to the 21-word range.

## Conventions

T_0 = 1 and T_(b+1) = a^T_b. For b >= 1, k_b is the exponent of 10 dividing
D_b, and s_b = -(D_b / 10^k_b) modulo 10, with representative 1 through 9.
The minus sign measures the old tower digit minus the next tower digit.

**V_1 = k_1**. For b >= 2, V_b = k_b - k_(b-1). The algebraic value T_0 = 1
does NOT mean that v_10(a-1) should be subtracted at height one. Leading
zeroes are included in the matching-digit count. In particular, k_2(5)=5.

B is the first height from which ALL subsequent speeds equal the limiting
speed. Four phases starting at B are reduced to period two or one when
appropriate. The program computes B from proved formulas, not by observing
a short run of equal increments.

The modular phase word instead starts at H = nu(a)+2. It can be accessed
through the `modular_word` function in `code/phase_tetration.py`.

## Source files and certificates

`code/phase_tetration.py` implements exact residues modulo 2^u 5^v,
capped towers, local valuations, exact onsets, phase words and the sharp
Chinese-remainder family. No floating-point logarithms or guessed period
reductions are used.

`code/verify.py` implements the test suite and a second modular algorithm.
The second algorithm uses a different reduction path, but shares the capped
tower helper; the direct-integer tests check that helper separately. The
finite tests supplement the proof and do not by themselves establish any
universal statement.

`data/witnesses.csv` contains all 21 witnesses with onsets, speeds and exact
residues certifying the first phase. Subsequent phases follow from the proved
multiplier or balanced recurrence. `data/modular_witnesses.csv` contains
all 28 prescribed-anchor witnesses. `data/sharp_onsets.csv` contains the
large-onset examples. `data/verification.json` and `.txt` record the full run.
The saved timing is environment-specific, not a performance guarantee.

## Build the PDF

Install a TeX distribution containing the usual AMS packages, newpxtext,
newpxmath, tcolorbox, microtype, geometry, fancyhdr and hyperref. No BibTeX
step is needed; the bibliography is in the source.

```text
pdflatex -interaction=nonstopmode -halt-on-error tetration_phase_classification.tex
pdflatex -interaction=nonstopmode -halt-on-error tetration_phase_classification.tex
```

Alternatively run `bash build.sh` or `pwsh -File build.ps1`. Neither script
installs software or changes user settings. No font files or third-party
papers are distributed in this archive.

## Additional proven consequences

Each of the words 9, 19, 3971 and 7931 occurs with natural density 1/900
among the positive integers. A constructive family has onset r+2 for every
r >= 3, showing sharpness of the known general onset bound. The word can
be computed in polynomial time in the input base's bit length; the article
gives a coarse complexity proof, not a claimed optimal bound. Practical
interpreter recursion and memory limits still apply to the implementation.
