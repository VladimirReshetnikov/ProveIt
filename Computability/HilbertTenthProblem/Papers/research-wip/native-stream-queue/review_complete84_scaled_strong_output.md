# Independent review of the 84-operation scaled output

**PASS.** The complete circuit costs **84=47M+37A**, retains **18 strictly
positive witnesses** and the same ordinary input and fixed-program numerals,
and has **uniform exact degree 187**. Its entire positive integer zero set is
identical to that of the reviewed 85-operation parent. The comparison-system
bound remains 74; no unrestricted circuit optimum is asserted.

The [author proof](complete84_scaled_strong_output.md) and complete source
change the polynomial by an everywhere-positive factor on the allowed domain.
This is a saving across the strong and auxiliary blocks. It does not contradict
the earlier local five-gate lower bound for the exact quotient producer V,
which remains unchanged.

## The complete algebra and positive domain

Use Delta for the code's already-computed `A`. Put `t=i*c²`, and note that
`Ac2=Delta*c²` is already paid and remains used by the main norm. Previously,

    t=i*c²; t²; Q=Delta*t²; Kaux=Delta*Q; Ns=f²−Q

cost four multiplications and one subtraction. The new schedule is

    S=i*Ac2; Kaux=S²; Df=Delta*f²; scaled_strong=Df−Kaux.

It costs three multiplications and one subtraction. The square of f remains
paid and used by the quotient block. Exact polynomial identities give

    Kaux_new=Kaux_old,
    scaled_strong=Delta*Ns.

All six other factors, including the complete auxiliary norm and the quotient
V, retain their values. The six factor-product gates are unchanged. Replacing
the final subtraction of 1 by subtraction of Delta therefore gives

    F84=Delta*F85

over every commutative ring, on the identical supplied coordinate tuple.

On the allowed positive interface, the literal source computes
`q=(B−1)J+1>0`, `X=wq>0`, `Y=sq³>0`, and `a=XY+Y>0`. Thus
`Delta=a²+4a+3=(a+1)(a+3)>0`, before imposing any equation. Consequently
`F84=0` if and only if `F85=0`. This transfers the full positive-zero theorem
with the identity coordinate map. It needs no new inverse division, Pell
rank assumption, index-sign argument, auxiliary existence theorem, or input
encoding. The parent's ordinary-input universality follows on precisely its
existing valid fixed-program slices.

The new strong factor equals Delta at zeros. One must not begin by treating
all seven new factors as integer units. First recover the old polynomial zero
using Delta's positivity, then invoke the parent theorem. On unrestricted
signed tuples Delta can vanish, so unrestricted signed zero equivalence is
false. The author explicitly checks that excluded boundary.

## Independent source and degree checks

The [independent helper](review_complete84_scaled_strong_output.py) and
[receipt](review_complete84_scaled_strong_output.json) read pinned data only.
No author or predecessor Python is executed. The helper reconstructs the full
84-row map from the saved parent, checks the three deleted private registers'
complete consumer sets, and verifies all 79 unchanged definitions, both
interfaces, every live supplied port, and all seven finalizer operations.

At eleven explicitly verified independent cuts, a separate sparse coefficient
engine recursively expands the actual old and new output graphs. It proves
the auxiliary coefficient identity, the unchanged auxiliary factor, the scaled
strong factor, and the complete multiplier relation. This is an all-value
identity: the independent cuts can be replaced by their actual paid expressions
without imposing any zero equations. Forty full signed evaluations, including
twenty rational assignments, supplement the coefficient proof; they are not
materialized positive halting witnesses.

The parent's exact degree is 175. Delta has exact degree 12 and leading form
`w²s²Q⁸`, where `Q=(B−1)J`. Multiplication of nonzero leading forms gives exact
degree 187 uniformly on every admissible fixed-program slice. In particular
the new leader contains

    −32*(B−1)^112 * J^112*h*rho*delta²*i⁴*eta^13
        *w^18*s^31*transport_quotient*auxiliary_quotient²*f²,

whose coefficient is nonzero since B−1>0. Direct gate propagation gives only
the looser upper bound 197. Two independent full univariate expansions, using
different lines and moduli from the author, attain degree 187 with coefficients
422670 modulo 1000033 and 272315 modulo 1000037. Their complete leading values
also match the stated uniform formula. Primality is unnecessary for the
integer-polynomial nonvanishing implication.

Root read the entire author source and proof. A separate mathematical reviewer
checked the positive-domain transfer and literal consumers, and cross-read the
independent checker. Fresh normal and optimized exact receipt replays passed
for both author and review. The change improves the minimum operation count by
one while increasing degree from 175 to 187; the lower-degree 85/175 and other
reviewed tradeoffs remain available.

From any directory:

    python3 review_complete84_scaled_strong_output.py --root ABS_WIP \
      --expect review_complete84_scaled_strong_output.json

Before installation, add `--author-root /tmp`. Checks use explicit exceptions
and recursively type-exact receipts. The source/receipt/proof pins are recorded
in the review receipt, together with all authenticated author dependencies.
