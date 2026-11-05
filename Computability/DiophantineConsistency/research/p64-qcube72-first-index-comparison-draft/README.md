# First Pell index is below the main index

`FreeMainFirstIndexComparison.first_lt_main` proves `n<m` in every IΣ₁
model, from `X>0`, `Y≥2`, `eta>0`, the first Pell-coordinate identity
`2*ycoord n (2*(X*Y*Y−1)+1)=k`, and the main-coordinate identity
`ycoord m (X*Y+Y)=k*Y+eta`. It isolates the comparison argument used in
`P72Exact.index_window` and does not assume its old early carrier
congruence. This generic lemma does not itself extract the identities from an
actual graph zero, prove `2n=R+1`, or establish a reverse existence result.

Attempt02 passed with Lean exit 0, stable direct guards, and the axiom report
`[propext, Classical.choice, Quot.sound]`, without warning or `sorryAx`. The
source header calls it an unchecked draft but these exact bytes were checked.
The direct input object is `ArithmeticAdaptiveIndexComparison2011` from the
captured-provider library; transitive/dynamic ancestry and sampled resource
monitoring remain limitations, so this is not a source-only rebuild.

| Artifact | SHA-256 |
| --- | --- |
| `FreeMainFirstIndexComparison.lean` | `05a40cc42e40d229e3b18cc57b8585268488858ec8fa1e10465c4e1b25d64788` |
| `check02.py` | `24ca5c3887d0f45073db05c4626d65743721933724e44d34da17178ef928664e` |
| `observations/attempt02/compile.log` | `4e423a199a364400cd913793d46b7a78a10220f4b920d603dc247fdc29a1a61f` |
| `observations/attempt02/result.json` | `4b2a609261cd30840ec9490e5b37f1155864f480105af706d247448dd05f6322` |
| `/tmp/p64-qcube72-first-index-comparison-priority-check02/FreeMainFirstIndexComparison.olean` | `b047e0649391b7f65d2b2ec83d4f8fda46566adcc22abf8bd38f4bd566a3f6d6` |

The check used a 2,400 MiB Lean limit, 120-second timeout, sampled
process-group RSS limit of 3.5 GiB, minimum 10 GiB available host memory,
and low CPU and I/O priority. Attempt01 failed because the namespace
containing `y_strictMono` was not open; it produced no object, and the
failed axiom report contains `sorryAx`. Its exact source, runner, log and
receipt are retained in `observations/attempt01/`.
