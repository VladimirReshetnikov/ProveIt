# Verification scripts

These programs are supporting evidence for the canonical
[`Rvachev_Up_Fourier_Decay`](../Rvachev_Up_Fourier_Decay/Rvachev_Up_Fourier_Decay.tex)
article. They were retained from the two independent audits after the source
documents were consolidated.

They are **not proofs**. Exact symbolic calculations are identified below;
floating-point stability, collocation convergence, Monte Carlo output, and a
long decimal expansion do not constitute a certified enclosure.

## Contents

- `stage1.py`–`stage3.py`: original comparative-audit calculations for sinc
  products, transfer matrices, shell means, fluctuations, extrema, and the
  exact rational Sturm certificate embedded in the article.
- `stage4b.py`: corrected long-orbit LIL experiment and high-precision constant
  summary. The former `stage4.py` used a nonuniform initial-point sampler and
  was retired; its immutable historical copy is available at commit
  `2e3567feb14947ee3ebcdab11adca64e746ad26f`.
- `stage5.py`, `stage6.py`, and `stage6b.py`: finite-level phase-profile,
  peak/area, RMS, Parseval, and subleading-spectrum experiments. The `b`
  scripts supplement rather than replace their unsuffixed predecessors.
- `stage7_spectral.py`: high-precision transfer-operator collocation. It
  **overwrites** `constants.json`.
- `stage8_profile.py`: finite-level profile calculations; it reads the sibling
  `constants.json`.
- `stage8b_feature_zoom.py`: fine profile windows; it imports
  `stage8_profile.py` and **overwrites** `feature_zoom.txt`.
- `constants.json` and `feature_zoom.txt`: captured outputs used to audit the
  numerical constants and narrow finite-level profile features.

The experiments require Python 3 with `numpy`, `scipy`, `sympy`, and `mpmath`.
Some stages allocate millions of samples and may require substantial memory
and time. Run them from this directory so sibling data paths resolve as
intended. If reproducibility matters, run output-writing stages in a disposable
copy and compare the result with the committed capture before replacing it.

The article's correction ledger is authoritative when an old script comment,
finite-level sample, or report prose conflicts with a proved statement.
