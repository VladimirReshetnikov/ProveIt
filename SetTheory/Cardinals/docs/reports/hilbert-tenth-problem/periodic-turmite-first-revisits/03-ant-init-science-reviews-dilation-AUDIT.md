# Independent audit of the fixed binary digit-dilation bridge

## Verdict and scope

The proposed bridge and the emitted six arithmetic DAGs are mathematically sound under their stated input domains. The exponentiation calls can genuinely be replaced by the displayed finite Pell macro. No unknown Diophantine relation, variable-length bit family, or uncharged variable exponent remains inside these DAGs.

The recoder domain is **C >= 2**, Raw >= 1. The exponent macro actually works for base >= 1, exponent >= 0, positive output, although its author's docstring promises only base >= 2. All seven recoder calls satisfy the narrower promised domain. The wrapper's inherited G is at least 2. A claim covering C=0 or C=1 without changing the recoder would be false or unsupported.

Upstream Lean was read as source data only. Mathematical regression checks are independent newly written Python. The newly authored local checker was separately source-reviewed and executed for final read-only replay and tamper tests. No upstream Lean, upstream program, or saved schedule was executed; no publication or upload occurred; the separate literal ant/history dependencies were not re-proved.

## 1. Exact primary source

Read-only primary source:

https://github.com/leanprover-community/mathlib4/blob/ac77769fabe23cb237559e7f56578dbead91499f/Mathlib/NumberTheory/PellMatiyasevic.lean

- Commit: ac77769fabe23cb237559e7f56578dbead91499f
- Git blob: 6ede8ed67569fc1ddf2b4c09f0feb30ca42fca7e
- Exact file bytes: 39,986
- SHA256: 993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a
- `Pell.matiyasevic`: lines 760-847
- `Pell.eq_pow_of_pell`: lines 860-928

The saved local file has been checked against the Git blob, not merely assigned a local hash. See primary_source_pin.json. An initial local capture added a trailing newline; that was corrected before these pins were recorded.

## 2. EXP macro: all-input equivalence and exact domains

Let b >= 1, e >= 0, z >= 1. Put k=e+1 and m=bz. The desired equality is equivalent to b^k=m, since b is nonzero.

The 25 positive witnesses are:

w, aMinus1, T, g, x, y, u, v, s, t, betaMinus1;
three Plus-adapted nonnegative slacks w-b, w-k, y-k;
the positive slack T-m;
positive qb and qv;
eight Plus-adapted nonnegative quotients, in four pairs.

Interpret a=aMinus1+1 and beta=betaMinus1+1. The 15 equations are exactly:

1-3. x^2=1+(a^2-1)y^2, u^2=1+(a^2-1)v^2, s^2=1+(beta^2-1)t^2
4. beta=1+4y qb
5. beta congruent to a modulo u, expressed using a pair of nonnegative quotients
6. v=y^2 qv
7. s congruent to x modulo u, using a paired quotient
8. t congruent to k modulo 4y, using a paired quotient
9-12. y=k+(y-k), w=b+(w-b), w=k+(w-k), T=m+(T-m)
13. a^2=1+((w+1)^2-1)(wg)^2
14. 2ab=T+b^2+1
15. x congruent to y(a-b)+m modulo T, using a paired quotient

A congruence A congruent to B modulo M is represented as A+M q1=B+M q2, q1,q2>=0. It requires no sign assumption on A-B. All displayed squared-Pell equations translate exactly into the natural-subtraction equations of the cited source, since the difference equals 1 rather than 0.

### Soundness

The first twelve equations provide every hypothesis of `Pell.matiyasevic` for index k, without its trivial-index branch. Indeed a,beta>1; k<=y; v>0; beta congruent to 1 modulo 4y; y^2 divides v; and the other three required congruences hold. Therefore x=x_k(a), y=y_k(a).

The growth equation and w>=b,k>=1 force a>b. To see this, classify the Pell solution for parameter w+1: a=x_j(w+1), wg=y_j(w+1). As a>1, j>0. The standard Pell congruence y_j(w+1) congruent to j modulo w implies w divides j. Thus j>=w>=b and a> b, for example from a>= (w+1)^j. Consequently a-b in the polynomial equations is precisely the natural subtraction in `eq_pow_of_pell`; there is no missing inequality or truncation case.

All hypotheses of the positive-base, positive-exponent branch of `eq_pow_of_pell` now hold: k>0, b>0, a>1, m<T, b<=w, k<=w, the growth equation, and the final congruence. Thus b^k=m=bz and cancellation gives z=b^e.

### Completeness and positive restrictions

Use the source's constructive proof with w=max(b,k), a=x_w(w+1), and g=y_w(w+1)/w. Here w>=1, a>1, and g>0. Choose x=x_k(a), y=y_k(a). Since k>=1, both are positive. Take u=x_(2ky)(a), v=y_(2ky)(a), and the source's CRT beta>1; then s=x_k(beta), t=y_k(beta) are positive. The source proves all required divisibilities and congruences.

Because beta>1 and beta=1 modulo 4y with y>0, qb=(beta-1)/(4y) is genuinely positive. Because v>0 and y>0, qv=v/y^2 is positive. The source proves m<T. Every nonnegative slack and signed quotient is represented by the stated positive adapter. This establishes existence of all 25 positive witnesses, including e=0 and b=1; no zero witness has accidentally been forbidden.

## 3. Deterministic margins in the recoder

For the unique sentinel length n and payload x, write E=2^n, P=C^n and Raw=E+x with 0<=x<E. The emitted equations enforce these inequalities using a nonnegative rawPayloadPlus adapter and the positive rawSlack. Both are necessary: merely defining x=Raw-E and imposing x<E would not enforce x>=0.

The auxiliary radix is

B=2^(CP+2).

As C>=2 and P>=1, CP+2>=C+P+1. Hence B>C+P and, since P>=E, also B>E+2. Its exponent is positive, so B is a power of two with separated binary positions.

The equation B^n-1=(B-1)U gives U=sum_(i<n) B^i, including U=0 when n=0. Thus U has binary ones exactly in the distinct positions (CP+2)i.

## 4. Coefficient extraction and the omitted D<=U inequality

Let L=2^(U+1), Y=L^D and Z=(1+L)^U. Every binomial coefficient binom(U,j) is <=2^U<L, so the binomial expansion is literally the base-L expansion of Z, with no carries. The emitted coefficient equation is

Z=(qL+c)Y+r,

where q>=0, c=2h+1, 0<c<L, and 0<=r<Y. The bounds are paid positive slacks. Euclidean uniqueness forces c to be the coefficient at index D.

No explicit equation D<=U is needed. The carry-free expansion gives Z<L^(U+1). If D>U, then Y>=L^(U+1)>Z, but the coefficient equation with c>=1 implies Z>=Y, a contradiction. Thus D<=U follows. Equivalently, every base-L digit past index U is zero and cannot be odd.

Modulo 2, (1+t)^U is the product over its binary one positions of (1+t^(2^j)). Uniqueness of binary expansions shows binom(U,D) is odd exactly when D's binary one positions are a subset of U's. Therefore D=sum_(i<n) b_i B^i for uniquely determined bits b_i in {0,1}. This supplies the Lucas-parity step directly, with no additional computational oracle.

## 5. Exact original word and both orientations

Let S2=sum b_i 2^i and F=sum b_i C^i. Then S2<E and F<P for C>=2.

Since B congruent to 2 modulo B-2, D congruent to S2 modulo B-2. Both x and S2 are in [0,E), and B-2>E. The emitted raw remainder equation thus forces x=S2. Consequently the sentinel length n is the ordinary binary bit length minus one; leading zero payload bits remain part of the word.

For the forward recoder, B congruent to C modulo B-C. Its value v is in [0,P), by value+outSlack=P, and P<B-C. Thus the ordinary remainder identity forces v=F.

For reversal put R=sum_(i<n) b_i C^(n-1-i), with R=0 when n=0. Then

P D = C^n sum b_i B^i congruent to sum b_i C^(n-i) = C R modulo BC-1.

This polynomial congruence uses only i<n; there are no negative exponents. Both Cv and CR are <CP<BC-1, so the reverse remainder equation forces Cv=CR and, since C>0, v=R. Conversely its quotient is nonnegative: termwise C^n B^i >= C^(n-i), and the difference is divisible by BC-1. All forward and raw quotients are nonnegative as well because B>C>=2.

For n=0: E=P=1, Raw=1, U=D=v=0, L=2, Y=1, Z=c=1, r=q=0. The positive slacks and Plus adapters admit these values. All-zero nonempty words likewise give D=v=0 while n, powers, and sentinel code preserve the length.

## 6. Pair interface and positive-output caveat

RawLeft=2^L+sum ell_j 2^(L-1-j), RawRight=2^R+sum r_j 2^(R-1-j), nearest symbol indexed j=0. Reversal on the left yields sum ell_j G^j; forward on the right yields sum r_j G^(R-1-j). The pair's equations give exactly

A=G^(L+R), B=G^R,
T=G^(R+1) sum ell_j G^j + sum r_j G^(R-1-j).

The same G port is used throughout. A*G supplies G^(L+R+1) in one further multiplication. A and B are positive, but T may be zero. The standalone ledger treats A,B,T as free ports. A positive-only exposed T port must be TPlus-1, with its adapter charged; internalizing all three ports costs three positive witnesses A,B,TPlus. Alternatively a composed wrapper can directly alias the three expression outputs, removing all three interface equalities and introducing no port witnesses. These are different ledgers and must not be conflated.

## 7. Independent graph count and finite checks

Read-only parsing of the six final-evidence JSONs checked every gate, topological reference, operation type, witness name and equation reference. It independently gives:

- EXP: 31 M + 39 A = 70 operations; 25 positive witnesses; 15 equations
- Forward: 224 M + 300 A = 524; 196 witnesses; 114 equations
- Reverse: 227 M + 300 A = 527; 196 witnesses; 114 equations
- Pair: 454 M + 601 A = 1055; 392 witnesses; 231 equations, including 3 free-output equalities
- Inline pair: 454 M + 601 A = 1055; 392 witnesses; 228 equations
- Positive-port pair: 454 M + 602 A = 1056; 392 internal witnesses; 231 equations, plus external positive A,B,Tplus ports

Each recoder has seven EXP calls plus 21 other positive witnesses and 9 other equations. In the pair, fourteen EXP calls account for 350 witnesses and 210 equations; the remainder is 42 witnesses and 21 equations. None of these counts includes a sum-of-squares conjunction, a degree-reduction lift, the periodic board wrapper, endpoint selection, or the parent's history interface.

Independent checks passed:

- 232 exhaustive small candidate packed words, including 158 rejected bit patterns
- 72 literal no-carry coefficient extractions
- 11,253 word/radix/orientation cases, including 11 empty-word cases
- 11 explicitly constructed complete positive EXP witnesses, including exponent 1
- all six literal graph counts and bound references, also under Python -O

The checks are finite supplements to the above all-input argument, not substitutes for it. Receipts are in this audit directory. The graph receipt pins the exact final-evidence JSONs reviewed. The final written PROOF.md was source-read and found mathematically correct, including its simpler elementary proof of a>w from the positive growth Pell equation. An additional 11 witness cases were evaluated against the actual emitted 70-gate EXP graph.

Final checker review identified coercive Python JSON equality, and the author corrected it using strict canonical serialization plus duplicate-key and nonfinite-number rejection. Final replay passed normally and under -O. Twelve mutation classes were rejected in both modes (24 negative runs): boolean and floating numerals, operator mutation, unbound operand, missing witness, changed output alias, missing equation, extra property, duplicate key, NaN, Infinity, and floating receipt count. Existing output directories were refused without mutation in both modes; a fresh generated evidence directory was byte-identical. All author-directory files remained unchanged during this audit.

Final reviewed author script SHA256: 921dd97e3553d6338538faaa416daaade4e1d72ed59555516859bf8e7b36371d. Final reviewed author PROOF.md SHA256: 6ada76c9a076d08a2b3ec448ac68dff9b7b76d0cf8fc616ce86ed0706249787a. The final-manifest.json was checked entry by entry. See independent_final_cli_receipt.json.

The Apache 2.0 LICENSE from the same mathlib commit is preserved as LICENSE.mathlib, exact 11,357 bytes, Git blob 8dada3edaf50dbc082c9a125058f25def75e625a and SHA256 b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1.
