# Independent proof review: sharp sine-block Markov lift

**PASS within the stated coordinate and mask classes.** I read the complete frozen author note and independently challenged the construction, invariance, both sharpness claims, positivity, small-denominator example, and arithmetic scope. No correction is requested.

## Pins and coverage

| File | SHA-256 | Scope here |
|---|---|---|
| `/tmp/markov_sine_lift.md` | `7b30acebde3c5576773e92030242e4e8db1d00530fa9d7733b4ac8796270d1b2` | Full mathematical proof and qualifications |
| `/tmp/markov_sine_lift_checks.py` | `f720bead0b2159f091a4b9508f01de8218802e6cabe2c04a63f6f6ee19c556cd` | Byte authentication only |
| `/tmp/markov_sine_lift_checks.json` | `ce071908f9eb089e96904cafce6601b6e24a981a34b50f674ae28354e5969cb1` | Byte authentication only |
| `/tmp/markov_mask_matrix_lift.md` | `5dca0ea91dc1d05b7e1a784e2933a67c059e99f3db0dad74f8491849345e69e6` | Previously and freshly read full finite-interface proof |
| `/tmp/review_markov_mask_matrix_lift.md` | `4b371b8edc261c8cd6cc4bbd3e86c2b0133bfbf715365d6726c1292face8214c` | My inherited bounded review |

The Fourier formula is inherited only at the already reviewed source lines368–423 of `holder_zygmund_spectra.tex`, SHA-256 `98bc2920135319f1d9b72b14c180112fdbae39971d2cdd9698e3dc4aed4b63da`. I do not recertify its infinite-dimensional spectral theorems. No author, predecessor, archived, supplied, or frozen helper/source was executed or imported. The finite sample counts in the new receipt are author evidence, not independently replayed results.

## Construction and positivity

For an even real mask, subtracting the two input-character images gives sine coefficient `a_(bk-m)-a_(bk+m)` and cancels the constant coefficient. At `b=r+1`, `bk+m=b(k+1)-(b-m)`, so the proposed backward recursion exactly solves this difference for every entry of `M/q`. The frequencies `bk-m` are precisely the positive nonmultiples of b below br, with no repetitions. Thus normalization is automatic, and `q=2 max sum|C|+1` gives the strict lower bound `1/q` for every mask.

The bound `(|m|+|j|)/b<r+1` excludes all frequencies outside the stated block. Evenness cancels constants and permits the two character halves to interact without introducing a cosine component. The real sine block, rather than either separate complex character block, is the invariant object. The wholly zero family gives `q=1` and mask1, whose action on these sine coordinates is zero; the operator still fixes the constant function.

Expanding the triangular recurrence yields the displayed row sum formula. Each matrix row j occurs at most j times in the coefficient L1 bound, proving `sum|C|<=r sum|M|`. The possible increase in denominator is correctly retained as a tradeoff.

## Sharpness in the declared interfaces

For every normalized Markov mask, direct substitution gives `T_a sin(2*pi*b*x)=sin(2*pi*x)`. If `2<=b<=r`, this fixes the image of the b-th input sine to the first sine. It is incompatible with the b-th column of `I/q` for any nonzero scalar q. This proves the claimed minimum integer dilation for arbitrary matrices in the standard consecutive sine basis. Neither evenness nor finite support is needed for this obstruction; neither a different basis nor a restricted matrix family is ruled out.

For finite even masks at `b=r+1`, let N be the highest nonzero positive Fourier frequency. Normalization excludes multiples of b. Choose `m=b-(N mod b)` and `k=(N+m)/b`. The coefficient of the k-th output sine is `a_N-a_(N+2m)=a_N`. When `N>br-1`, this is a nonzero output beyond the purported invariant block, a contradiction. The constant-mask case is separately harmless. Hence no finite even high-frequency correction can preserve the block while repairing positivity.

Within the remaining support, the backward coefficient system is triangular with diagonal1, so it has the unique solution `C/q`. In particular `M_(r,1)!=0` forces the extreme coefficient `a_(br-1)` nonzero. This proves worst-case degree sharpness in that class, not a bound for arbitrary functional encodings or non-even masks.

## The two-matrix counter example and costs

For the displayed identity and decrement matrices, the recurrence gives exactly `C_I=[[2,0],[0,1]]` and `C_D=[[2,-1],[0,1]]`. Expanding `cos(2 theta)=2t^2-1` and `cos(4 theta)=8t^4-8t^2+1` independently reproduces both denominator5 identities. For the decrement mask, if `t<=3/4` then `2(1-t)>=1/2`; otherwise `(4t^2-1)^2>=25/16`. Strict positivity follows on the whole interval, not from sampled values.

At denominator4 and `t=3/5`, the numerator is exactly `-4/625`. Every smaller positive integer denominator further decreases that numerator, and finite-even uniqueness excludes an alternative coefficient repair at the same block, dilation, and denominator. Thus5 is the minimum positive integer denominator under those precise restrictions. Frequency4 is the exact maximum here; the generic degree5 need not be attained by every matrix.

The triangular coefficient transform takes `r(r-1)` additions after copying the bottom row. This is fixed mask compilation. It does not evaluate a variable word, decide its guards, bind an ordinary input, or encode a history. The direct matrix-vector bound remains an upper bound of `r^2` multiplications plus `r(r-1)` additions, with possible sparsity savings. Duration scaling `q^(-T)` remains in nonzero targets, and full-operator mortality remains impossible because constants are fixed. The sharper dilation/degree theorem therefore supplies a representation improvement without asserting an ordinary-integer compiler or operation-count improvement.
