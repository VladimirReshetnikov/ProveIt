# Draft proposed OEIS note — not submitted

This note is supplied for mathematical and editorial review. It should
not be treated as an accepted OEIS contribution or a peer-reviewed citation.

## A189281

Let a(n)=A189281(n). The asymptotic expansion

    e a(n)/n! ~ sum_{J>=0} c_J/n^J

has c_J in Z for every J. A finite formula is

    c_0=1,
    c_J = sum_{h=1}^J (-1)^h sum_{j=0}^h
            j! binom(h-4,h-j) S(J-1,h+j-1),  J>=1,

where S is the Stirling number of the second kind (zero outside its
range) and binomial coefficients have their generalized integer meaning.
For each fixed M, truncation after c_M has error O(n^(-M-1)).

The proof uses normalized stable factorial moments R_h(n), with

    R_h(n)=24 (n-h+1)^(fall h-4)/n^(fall 2h), h>=4.

This proves the rational-collapse conjecture in ProveIt's earlier report.
It does not prove the separate conjectured recurrence for a(n).

The article also proves integrality for every directed offset pair r,s,
including A189282, A189283, and A189284. The weight j! above is replaced
by (r-1)^(rise j)(s-1)^(rise j)/j!, and 4 by r+s.

## Citation status

The supplied article is an unrefereed AI-assisted research draft with
complete written proofs and exact verification scripts. A stable public
citation and independent review should precede an actual OEIS submission.
