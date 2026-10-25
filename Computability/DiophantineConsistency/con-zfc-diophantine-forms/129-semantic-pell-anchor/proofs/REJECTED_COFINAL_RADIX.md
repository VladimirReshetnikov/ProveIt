# Rejected measured alternative: an unindexed Pell radix

This bounded experiment replaces the exact radix power `q=N^K` by a cofinal
Pell ordinate.  It does not improve the final quartic.  The constructor is a
separate copy of the root's then-current `build_combined.py`, with one
intercepted power call.  The main constructor was not edited.

## Elementary replacement lemma

Assume N,K are natural integers at least two.  Put r=NK and impose

    q = r(z+1),
    P^2 - ((r+1)^2-1) q^2 = 1,

with P,z natural.  Pell classification gives

    P=X_j(r+1), q=Y_j(r+1), j>0.

Since `Y_j(r+1) = j (mod r)` and r divides q, r divides j, so j>=r.
The recurrence gives `Y_j(a)>=a^(j-1)` for a>=2 and j>=1.  Consequently

    q >= (r+1)^(r-1) >= N^K,

because r+1>N and r-1=NK-1>=K.  Also N divides q.  Conversely choose j=r;
then r divides Y_r(r+1), so `z=Y_r(r+1)/r-1` is a natural witness.

Every use of the old equality `q=N^K` in the binomial/CRT proof needs only
`N|q` and `q>=N^K`.  All exact denominator powers remain unchanged.  The
common modular root congruence remains soluble, since every prime of N also
divides q.  The new q is chosen before the principal Pell base A, so this
replacement creates no witness-choice cycle.

## Matched result

The matched parent uses dominant modulus, the derived-label semantic anchor,
standard coordinates, contraction cap64, and protected `index_cap.Y`.

| Measure | Exact radix parent | Cofinal radix experiment |
|---|---:|---:|
| Exact power requests | 6 | 5 |
| Raw natural coordinates | 344 | 343 |
| Raw quadratic rows | 293 | 292 |
| Contracted coordinates | 234 | 236 |
| Contracted quadratic rows | 183 | 185 |
| Collected quartic terms | 9095 | 9124 |
| Coefficient height | 87742206 | 87742278 |

All raw affine-export substitutions, dependency pruning, raw expanded
coefficients, and target liveness were independently checked.  The additional
Pell frame removes an exact-power call but prevents three eliminations in the
subsequent natural projection.  The final equation is therefore larger.

The incoming `ConZFC_Cofinal_Witnesses_2026-10-24.zip` uses cofinal proof
horizons and reuses a factorial numerator for beta moduli.  Its README does
not give this radix replacement.  This limited comparison is not a claim of
literature-wide novelty.  No further variants were searched in this experiment.
