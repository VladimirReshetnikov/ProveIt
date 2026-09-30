# At the Critical Line
## Continued fractions and sharp Riesz summation of resonant transseries

Research article prepared for Vladimir Reshetnikov, 29 September 2026.

Read **article.pdf** (23 pages). The editable source is **article.tex**.
The ZIP includes the two table inputs needed to compile the source.

## Results

The article answers Question 1 in ProveIt's `Resonance_Block_Summation_Transseries`
report at the pinned repository snapshot below.

For two irrationally related sine lattices, numerator degree D >= 2, and
0 < b = beta(alpha) < infinity, let p_k/q_k be the continued-fraction
convergents and A_k = q_k^D q_{k+1} exp(-b q_k).

* Increasing-action raw convergence on Re z = b is equivalent to A_k -> 0.
  Absolute convergence is equivalent to sum A_k < infinity.
* The two separately indexed lattice sums instead converge exactly when
  sum (-1)^(p_k+q_k+k) A_k exp(-i Im(z) q_k) converges.
* Explicit continued-fraction constructions realize absolute convergence,
  conditional convergence, opposite divergent separate sums, two-point
  raw partial-sum cluster sets, and unbounded spikes at every positive b.
* The j-th differentiated raw series has the corresponding criteria with
  q_k^j A_k. This concerns the representation, not the analyticity of the
  normally convergent block sum.
* For d fixed sine lattices, integer Riesz order m >= d-1 recovers the block
  sum throughout Re z > 0, with a finite derivative bias and a uniform
  O(T^(D-m) exp(-sigma T)) remainder. No Diophantine condition is needed.
* The threshold is sharp for gap-independent, period-uniform control.
  Continuity at a collision exactly on the cutoff requires m >= d.
  Richardson extrapolation removes the derivative bias. A local inverse
  stability theorem transfers the exponential accuracy through inversion.

There are ten further research projects, a proof-dependency map, a precise
comparison with the predecessor, and primary-literature references.

## Mathematical and verification status

The new statements have conventional proofs in the article. They have not
been formalized in Lean or independently peer-reviewed. No global priority
claim is made. Classical continued-fraction theory, divided differences,
Riesz means, interpolation, and local inverse estimates are credited.

The executed verification contains **192 exact assertions** and **49 numerical
assertions**, all passing, at **110 decimal digits**. The numerical work uses
ordinary high-precision arithmetic, not directed-rounding intervals.
Finite continued-fraction tests do not certify an infinite exponent or the
infinite examples; the proofs establish those results.

The Riesz sharpness claim is about uniform control as periods approach a
collision, not the minimal order for every individual fixed d-lattice input.
Raw ordinary convergence at beta = 0 fails the term test; beta = infinity has
no finite critical line, but the Riesz theorem still applies in Re z > 0.

## Files

- `article.tex`, `article.pdf`: source and compiled article.
- `verify.py`: exact finite checks and numerical reproduction.
- `results/`: recorded JSON, CSVs, text summary, and two TeX table inputs.
- `SOURCES.md`: pinned source and primary-literature provenance.
- `QA_REPORT.md`: build, numerical, visual, and scope checks.
- `requirements.txt`: pinned Python dependency versions.
- `build.sh`, `Makefile`: reproduction commands.

No third-party source corpus or font files are included.

## Reproduce

Use Python 3.10 or newer, the dependencies in `requirements.txt`, and a TeX
Live installation providing the packages named in `article.tex`.

```sh
python -m pip install -r requirements.txt
sh build.sh
```

`build.sh` writes regenerated checks and TeX intermediates below `build/`,
compiles using the recorded table inputs in `results/`, and replaces
`article.pdf`. It does not overwrite the recorded verification data.
Set `PYTHON` to select the Python interpreter.

Separate targets:

```sh
make verify  # regenerate checks under build/results
make pdf     # typeset the article from recorded tables
```

To regenerate the recorded tables intentionally, use:

```sh
python verify.py --outdir results
```

The verification program makes no network requests. Its numerical residue
routine handles simple poles only. It rejects sine phases resolved as
integers (exact collisions or gaps below the current working resolution).
It is not a stable general-purpose confluent-residue implementation.

## Repository snapshot

`VladimirReshetnikov/ProveIt`, commit
`3d5973524506411392a911470b5ddc35521568ea`.

Primary predecessor:
`Analysis/Transseries/docs/series-and-transseries/Resonance_Block_Summation_Transseries/article.tex`.

No repository files were changed.
