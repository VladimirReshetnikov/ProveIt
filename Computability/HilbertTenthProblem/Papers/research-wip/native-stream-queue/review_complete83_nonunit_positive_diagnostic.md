# Independent review of the positive nonunit83 diagnostic

**PASS.** The [author's complete assignment](complete83_nonunit_positive_diagnostic.md) is an exact zero of the actual 83-gate polynomial, with all 18 witnesses, the ordinary input and all six supplied fixed numeral values positive. Its factors are

    (1,1,1,1,1,-675,-1), Delta=675, output=0.

This is a fully materialized arithmetic diagnostic on **invalid compiler numerals**. It does not refute the soundness of the 83 candidate on valid program slices, supply a falsely accepted compiled input, or improve a universal operation bound.

The [independent checker](review_complete83_nonunit_positive_diagnostic.py) and [receipt](review_complete83_nonunit_positive_diagnostic.json) pin the final author trio and the frozen [83 source trio](complete83_free_coefficient_scout.md). They read these as bytes/JSON and execute no author or predecessor Python. The full author source and final note were read. One note-only clarification was requested and incorporated before these pins: the general divisor/sign paragraph now explicitly assumes Delta>0. No source or numerical receipt change was needed, and no finding remains.

## Independent source and tuple reconstruction

The saved diagnostic source, output, free-port list, witness list and fixed numeral list agree exactly with the actual frozen 83 packet. The review reconstructs every supplied value using fresh sequential second-order Pell recurrences, independently of the author's binary powering. It verifies all required divisions and both strict inequalities

    8k<c<9k, gamma>rho>0.

This establishes positivity of the two ratio slacks eta,zeta and sigma=gamma-rho as well as the other supplied coordinates. All 25 supplied hexadecimal values agree exactly with the author's saved values.

An independent interpreter evaluates every row of the actual source and compares all 83 computed registers with the saved signed hexadecimal values. All rows and all free ports are live. The full paid ledger is 83=46M+37A, with no deleted condition or changed finalizer. The largest supplied integer has 7,699 bits and the largest computed magnitude has 15,400 bits, confirming that the entire tuple and output were actually materialized.

The review also independently recovers the Pell indices by repeatedly multiplying a positive norm-one pair by A-sqrt(A²-1) until reaching (1,0). Every inverse step has nonnegative second coordinate strictly smaller than before. Applied to the computed source ports, this recovers

| Actual pair | Parameter | Recovered index |
|---|---:|---:|
| Main D,c |26|1,351|
| First tau,k/2 |257|855|
| Input mu,kappa |26|17|
| Auxiliary 26*abs(V),y_aux |26|3|

Thus the indices are independently checked from the evaluated tuple, not only reproduced from the author's declared parameters. These are ordinary Pell sequence indices of this diagnostic; they do not certify a compiled computation.

## Complete factor values and signs

The source computes

    q=2, X=2, Y=8, E=16, a=24, Delta=675, H=99.

The constructed first and main Pell pairs give their two factors +1. The input ports satisfy

    C=-3, W=-4,
    kappa=17+675*delta,
    mu=-4+24*kappa+99*rho,

and give the input factor +1. These are allowed negative **computed** values; no supplied witness is negative. The projection residues 2^1351=2 modulo 99 and 2^17=-4 modulo 99 are checked separately, together with the exact divisions defining the positive quotients.

The paid packing expression evaluates to

    R=(4-2-1)*(4-1)+(2694+2*2)=2701.

The positive h=(k-2702)/16 gives k-hE-R=1. Thus the first-index factor is also +1, although the actual main Pell index is 1,351 rather than this packed target 2,701.

With supplied S=26 and f=T=1, the source gives

    V=c*(Tf-1)-R*f²=-2701,
    Ns_scaled=675-26²=-1,
    Na=26²*2701²-(26²-1)*2703²=1.

The auxiliary identity is independently recognized at Pell index 3: abs(V)=4*26²-3 and y_aux=4*26²-1. In particular the auxiliary factor is +1 despite its negative computed root. The retained sheared transport expression is

    (1+1)*(-3)+2-1-670*(2-1)=-675.

The actual finalizer multiplies these seven factors to +675 and subtracts the actual discriminant 675. Its computed result is exactly zero. The transport factor is a nonunit negative divisor; the scaled strong factor is a negative unit. Positivity of the supplied values alone therefore does not force the intended individual factor values.

For an integer zero **with Delta>0**, the product equation does imply that all factors are nonzero integer divisors of Delta, each has absolute value at most Delta, and the number of negative factors is even. The diagnostic obeys all of these consequences. It shows that stronger unit/positive-sign conclusions need additional hypotheses. The explicit Delta>0 condition is necessary when formulating this statement outside the positive supplied domain.

## Compiler exclusions and exact scope

The diagnostic's six numeral values are positive, but they fail the fixed-program recipe in direct, checkable ways. Here B=Bm1+1=2 and q=2 fall below the required range. MC=2,694 fails 0<MC<B-1. The native unshifted mask MF0=MF-(B-1)=1 fails its strict range and its residue 4 modulo 8. The input offset 15 exceeds d=twice_cell_bits/2=1. These failures already exclude an admissible compiler slice; the author's additional K and input-length exclusions are consistent with the same diagnostic data.

No valid compiler theorem is invoked to interpret this tuple. In particular the negative transport value cannot be used as a counterexample to a proof whose hypotheses require valid masks and an actual fixed program. This is distinct from the earlier full-zero extension over valid accepted inputs: the present fixture exhibits nonunit/sign behavior by using inadmissible fixed numerals.

The review establishes only the exact source zero and the failure of a sign argument based on positive supplied coordinates/numerals without the remaining compiler conditions. It neither establishes nor rules out such branches on valid compiler slices.

## Replay

After installation, run from any directory:

    python3 review_complete83_nonunit_positive_diagnostic.py --root ABS_WIP --expect ABS_RECEIPT

During staging, add `--author-root /tmp` to select the frozen new diagnostic trio. The saved 83 parent resolves under ABS_WIP. `--output PATH` writes a stable receipt containing hashes of all reconstructed values, the recovered indices, full factor values, counts and concrete compiler exclusions. It need not duplicate the author's large arrays.

Fresh normal and `python3 -O` exact replays from `/` pass. All checks use explicit exceptions and recursively type-exact receipt comparison. No repository or frozen file is changed, and no archived code or historical suite executes.
