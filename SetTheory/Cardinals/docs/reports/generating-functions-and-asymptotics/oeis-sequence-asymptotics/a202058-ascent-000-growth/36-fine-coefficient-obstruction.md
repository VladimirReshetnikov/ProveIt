# The remaining coefficient-regularity obstruction

## Exact one-step identities

Under the compacted-state distribution of a uniformly sampled length-n word, let m=s+u and M_n=E_n[m]=a_(n+1)/a_n. The exact child operator satisfies

    T_op m = m²+m−s−k = m²+u−k,
    T_op s = ms+m−2s,
    T_op k = m(m+1)/2−s,
    T_op(m²)=m³+2m(m−s−k)+m−|s−k|.

Consequently

    M_(n+1)=M_n+[Var_n(m)+E_n(u−k)]/M_n.

Log-concavity of a_j/j! at j=n+1 is exactly the assertion

    (n+1)[Var_n(m)+E_n(u−k)] <= M_n².

The first three identities are polynomial, but the absolute-value term in T_op(m²) prevents a straightforward closed moment recursion. No inequality proving the displayed variance bound has been established here.

## What finite computation says

The inequality (j+1)a_j²>j a_(j−1)a_(j+1) holds exactly for every j=2,...,399; j=1 gives equality. Further exact checks show log-concavity of (T_op^j 1)(x)/j! for all 204 states with s+u<=8 and all tested centers j=1,...,15. These are evidence for a potentially stronger all-state preservation theorem, not its proof.

If global normalized log-concavity were proved, the known root limit would immediately imply a_n/(n! μ^n)>=1: all consecutive ratios of a_n/n! would decrease to μ and remain at least μ. Combined with the new upper theorem this would confine the logarithmic correction between 0 and O(log²n), excluding negative as well as positive stretched exponentials. It still would not identify the coefficient 2/3.

## Tempting stronger tools fail

The factorial-normalized sequence b_n=a_n/n! is not PF3. Its initial Toeplitz minor

    det [[b1,b2,b3],[b0,b1,b2],[0,b0,b1]] = −1/3

because b0=b1=b2=1 and b3=2/3. A total-positivity proof would therefore need a PF2-specific argument; PF∞ is false.

The length-seven doubled-letter polynomial is 1+21z+126z²+129z³ and has discriminant −84159, so that natural multiplicity refinement is not real-rooted. Coordinatewise lattice closure also fails: 001 and 010 are both cap-two ascent words, but their meet 000 is not.

These are exact obstructions to particular proof methods, not evidence that the desired normalized log-concavity statement is false.

## Why uniform function barriers do not finish the task

The proved uniform relation logF(t(q),x)=logψ(q,x)+O(q²) is strong enough for the coefficient upper bound because of positivity. For a lower bound it controls only a weighted sum of coefficients. The existing Chernoff argument extracts some coefficient in a broad window; the deterministic initial path and monotone extension to a specified index lose a term of order n^(2/3)(log n)^(5/3).

A full equivalent would require a local coefficient theorem or stronger regularity in addition to a sharper real/complex singular analysis. Neither a finite ratio fit, the root limit, nor positivity alone supplies these missing statements.
