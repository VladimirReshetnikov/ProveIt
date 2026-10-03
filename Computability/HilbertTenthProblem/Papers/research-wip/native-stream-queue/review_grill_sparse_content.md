# Independent audit of the sparse Grill content row

The [sparse compiler](grill_tag_sparse_content.md) passes a separate complete-source audit. Its final polynomial has the **same supplied integer zeros** as the scaled word-closure parent, on exactly the same coordinates. The complete polynomials themselves differ, and their unsquared versions have different positive-real zero sets.

The retained width residual is `r=A_t−2^t`; the new content residual is `e=B−x−Σc_i d_i A_i`. Direct telescoping gives the old content row `s=r+3e` without assuming Boolean heads. Consequently the entire correction is

```
F_old − F_new = r² + 6re + 8e².
```

For integer heads each unsquared Boolean factor `d(d−1)` is nonnegative. Thus both finalizers vanish precisely when their two squared rows and every Boolean factor vanish. The invertible row change proves both directions on all integer tuples, including signed ones. Positive input padding, all witnesses and the parent's possible post-halt extensions are unchanged. For squared Boolean factors the same row argument also preserves real zero sets. These are distinct domain claims.

The [independent checker](review_grill_sparse_content.py) authenticates the new source at SHA256 `3c2d0cf875f82e45062334dc8b42cb033d909afed5204bb9abd9547cff0e16f7`. It reuses the previously independent parent review's pinned general sparse-polynomial algebra, gate/liveness checker and causal word census. It does not call the new author's verification routine. Its new expected polynomial is constructed from closed prefix products and appended-word coefficients, independently of the emitted scaled recurrence. It then expands every emitted gate and checks the whole output, every residual, the off-zero correction, attained degree and complete cost.

The saved [review receipt](review_grill_sparse_content.json) records:

- 72 complete expanded sources and polynomial corrections across six programs, horizons 1–6 and both Boolean finalizers; 396 residual identities and 216 signed public evaluations.
- A census of all 12,276 head words through horizon ten, giving 247 positive closures, including 20 post-halt closures; all 494 evaluations and decodings across both finalizers agree with direct queue execution.
- Two rational witnesses separating the unsquared real zero sets in opposite directions, 38 malformed-call rejections and four defensive-copy checks.

The complete count is `11t+5−3z(t)`, consisting of `5t+2−2z(t)` multiplications and `6t+3−z(t)` additions/subtractions. Its saving against the parent is `2+2z(t)−t`, which can be negative. The exact degree remains `2t+2`: the width residual has a nonzero homogeneous term of degree `t+1`, and the sum of its square and the content square cannot cancel that degree over the reals. The source counts agree with this argument in every expanded case.

Root separately replayed the full author suite and obtained the saved receipt byte for byte, then ran this independent checker successfully. These checks support the general algebraic proof; finite enumeration is not a proof for all programs. The horizon remains external, and no universal decoder or improvement to the 87-operation benchmark is claimed.

From this directory:

```sh
python review_grill_sparse_content.py --expect review_grill_sparse_content.json
python grill_tag_sparse_content.py --expect grill_tag_sparse_content.json
```
