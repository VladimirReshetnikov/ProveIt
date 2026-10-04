# Counting all encoded positive integer gap initializations

4 October 2026. This is a separate, unnumbered arithmetic continuation of the primitive-initialization theorem in `../native-gap-halting-continuation-20261004/PROOF.md`, Section 6. It changes no earlier packet. Its conclusions concern all encoded triples, independently of a program, a time horizon, or halting.

## 1. Definition and input theorem

A positive integer triple g=(g_1,g_2,g_3), with D=g_1+g_2+g_3, is encoded when unique integers a,b>=0 satisfy

    g_1/D = 1/20 + 1/(10*2^a),
    g_3/D = 1/20 + 1/(10*2^b).

Uniqueness follows from the strict injectivity of a -> 2^(-a). The retained primitive theorem states that, for each ordered pair (a,b), all encoded triples are exactly the positive integer multiples of one primitive triple. With m=max(a,b), its total d(a,b) is

    20                 if (a,b)=(0,0),
    10                 if (a,b)=(1,1),
    20                 if {a,b}={0,1},
    2^(m+1)            if m>=2 and a=b=3 (mod 4),
    10*2^m             otherwise, for m>=2.

Here `a=b=3 (mod 4)` means both counters are congruent to 3, not necessarily equal. For every pair, including m=0,1,

    d(a,b) >= 2^(m+1).                                      (1)

Let A(N) count encoded positive integer triples with D<=N, for integer N>=0; A(0)=0. Distinct ordered counter pairs produce disjoint triples. Thus

    A(N) = sum_(a,b>=0) floor(N/d(a,b)).                      (2)

Only finitely many summands are nonzero. This counts triples, not witness tuples, successful computations, distinct counter pairs, or distinct total scales.

## 2. Exact floor formula and digital identity

Define F_b(n)=sum_(k>=0) (2k+1) floor(n/b^k), for integer b>=2 and n>=0. Then

    A(N) = F_2(floor(N/10))
         + F_16(floor(N/16)) - F_16(floor(N/80)).             (3)

Proof: there are 2m+1 ordered counter pairs with maximum m. First give them all the baseline scale 10*2^m. The exceptional pair (0,0) changes floor(N/10) to floor(N/20), while (1,1) makes the inverse change, so these corrections cancel exactly. The remaining exceptions have m=4k+3: among counters 3,7,...,4k+3, exactly 2k+1 ordered pairs have maximum 4k+3. Each replaces scale 80*16^k by 16^(k+1). Summing proves (3), using floor(floor(N/c)/b^k)=floor(N/(c*b^k)).

For the base-b expansion n=sum_j d_j b^j, set

    s_b(n)=sum_j d_j,    w_b(n)=sum_j j*d_j,

with both sums zero for n=0. The self-contained digital identity is

    F_b(n) = [b(b+1)n - (3b-1)s_b(n)]/(b-1)^2
             - 2*w_b(n)/(b-1).                              (4)

Indeed, expanding each floor gives

    F_b(n)=sum_j d_j * sum_(k=0)^j (2k+1)b^(j-k).

The inner sum is

    [b(b+1)b^j - (3b-1)]/(b-1)^2 - 2j/(b-1).

To verify this last expression without any external identity, its j=0 value is 1, and both it and the inner sum obey S_j=b*S_(j-1)+(2j+1). Substitution proves (4). No attribution or sequence-identification claim is needed for this elementary derivation.

## 3. Exact count at one total scale

Write J(N)=A(N)-A(N-1), for N>=1, and let v=v_2(N), the exponent of 2 in N. Then the shell count simplifies to

    J(N) = v^2                  if 5 divides N,
           floor(v/4)^2        if 5 does not divide N.       (5)

Direct divisor-scale proof: each primitive scale d dividing N contributes exactly one triple of total N. The same low-counter exchange used above cancels for divisor indicators. If 5 divides N, the baseline divisors 10*2^m have 0<=m<=v-1; their multiplicities sum to v^2, with an empty sum when v=0. For each special pair, its old scale 80*16^k and new scale 16^(k+1) have exactly the same divisibility condition v>=4k+4, since 5 already divides N. All special corrections cancel. If 5 does not divide N, no baseline scale divides N. Exactly the new special scales with 0<=k<floor(v/4) divide N, giving sum(2k+1)=floor(v/4)^2. This proves (5).

Consequently, represented total scales are exactly the multiples of 10 or 16. Their distinct-scale counting function is

    B(N)=floor(N/10)+floor(N/16)-floor(N/80)
        = (3/20)N+O(1).                                    (6)

The distinct-scale density 3/20 is different from the triple-count slope below. A scale N is repeated J(N) times when triples are listed in nondecreasing total.

## 4. Leading constant, nonnegative error, and sharp envelope

The absolutely convergent reciprocal sum of primitive scales is

    rho = sum_(a,b>=0) 1/d(a,b)
        = (1/10)*sum_(m>=0)(2m+1)/2^m
          +(1/16-1/80)*sum_(k>=0)(2k+1)/16^k
        = 3/5 + 68/1125 = 743/1125.                         (7)

The two low-counter corrections cancel again. For completeness, sum_(k>=0)(2k+1)x^k=(1+x)/(1-x)^2 for |x|<1: multiply the series by 1-x, obtaining 1+2*sum_(k>=1)x^k, then sum the geometric series. Absolute convergence also follows directly from (1).

Define E(N)=rho*N-A(N). Equation (2) gives a convergent nonnegative sum

    E(N)=sum_(a,b>=0) (N/d(a,b)-floor(N/d(a,b))) >= 0.        (8)

For N>=1 put L=floor(log_2 N). Splitting at maximum counter L, the (L+1)^2 pairs with maximum <=L contribute strictly less than (L+1)^2. By (1), the remaining tail contributes at most

    N * sum_(m=L+1)^infinity (2m+1)/2^(m+1)
      = N*(2L+5)/2^(L+1) < 2L+5.

Thus a completely explicit bound is

    0 <= E(N) < L^2+4L+6,                                  (9)
    A(N) = (743/1125)N - O((log N)^2).

In particular A(N)/N -> rho. This is a linear growth constant for triples as a function of total; it is not the density among all positive triples of bounded total, whose count is binomial(N,3).

Now let N_M=10*2^M, for M>=1. Every primitive scale with maximum counter <=M divides N_M, and none with maximum >M divides N_M. The two low-counter cases are covered by M>=1. Normal scales have a factor 5 and the relevant 2-adic exponent; special scales have exponent m+1, whereas v_2(N_M)=M+1. Therefore

    J(N_M)=(M+1)^2.                                        (10)

Some special scales with maximum >M can nevertheless be <=N_M. The claim is about divisibility, not size. In (8), all terms with maximum <=M vanish, so the remaining error is O(M); the exact formula is given next. Consequently

    E(N_M-1)=E(N_M)+(M+1)^2-rho = M^2+O(M).                 (11)

Since log_2(N_M)=M+O(1), (9) and these two subsequences give the sharp normalized envelope

    liminf_(N->infinity) E(N)/(log_2 N)^2 = 0,
    limsup_(N->infinity) E(N)/(log_2 N)^2 = 1.               (12)

Thus the uniform O(log^2 N) order cannot be reduced to o(log^2 N). There is no constant c with E(N)=c*(log_2 N)^2+o(log^2 N) for all integer N. This is the precise assertion intended here instead of an undefined claim about a "smooth correction."

## 5. Exact linear error on the power-of-two subsequence

For every M>=1, let r=M mod 4. Then

    E(N_M)=alpha_r*M+beta_r,                                (13)

where

    r       alpha_r       beta_r
    0       34/15         1261/225
    1       61/30         2329/450
    2       31/15         1189/225
    3       32/15         1223/225.

Derivation: F_2(2^M)=6*2^M-2M-5 by (4). For M>=3, put M-3=4q+t, 0<=t<=3, c=2^t, and h=floor(5c/16). The other two arguments in (3) are 5c*16^q and c*16^q. Their digit-sum difference is delta=4c-15h, and their weighted-digit-sum difference is q*delta+h. Here (delta,h) equals (4,0),(8,0),(1,1),(2,2) for t=0,1,2,3. Substituting (4) in (3) gives

    E(N_M)=2M+5+(47/225+2q/15)*delta+2h/15.

This yields the displayed table. The remaining cases M=1,2 are direct: A(20)=6 and A(40)=17, agreeing with (13). In particular, the exact left-neighbor error is (13)+(M+1)^2-rho.

## 6. Inverse quantile, explicitly with multiplicity

For n>=1 define

    D_n=min {N>=0 : A(N)>=n}.                               (14)

Thus D_n is the total of the nth encoded triple in an ordering by total, with ties in any order; the value N occurs exactly J(N) times. This is not the nth distinct represented total. It exists since the counter pair (1,1) alone supplies a triple at every positive multiple of 10.

From A(D_n)<=rho*D_n and A(D_n)>=n,

    D_n >= n/rho.

Also D_n<=10n. The defining inequality A(D_n-1)<n and (9) imply

    rho*D_n-n < rho+E(D_n-1)=O(log^2(n+1)),

with the finitely many small values absorbed in the constant. Hence

    D_n=(1125/743)n+O(log^2 n),                             (15)

and the deviation from n/rho is nonnegative.

The sharp inverse constants follow without estimating a rounding convention. Define the first and last ranks in the N_M block by

    n_M^first=A(N_M-1)+1,
    n_M^last =A(N_M).

Both inverse totals are exactly N_M. Equations (10) and (13) give

    D_(n_M^first)-n_M^first/rho
      =[E(N_M)+(M+1)^2-1]/rho
      =[M^2+(2+alpha_r)M+beta_r]/rho,

    D_(n_M^last)-n_M^last/rho
      =[alpha_r*M+beta_r]/rho.                              (16)

Both ranks are asymptotic to rho*N_M. Conversely, (9), (14), and (15) bound every inverse deviation above by (1/rho)*(log_2 n)^2+O(log n). Therefore

    liminf_(n->infinity) [D_n-n/rho]/(log_2 n)^2 = 0,
    limsup_(n->infinity) [D_n-n/rho]/(log_2 n)^2
      = 1/rho = 1125/743.                                  (17)

For comparison only, the inverse of the distinct-scale count B(N) in (6) is (20/3)n+O(1), with no multiplicities.

## 7. Scope, dependency, and checks

All conclusions are conditional only on the displayed primitive-initialization classification, already proved in the retained packet; Sections 1-6 above give the counting arguments in full. No digital-sum theorem is imported. The retained source's SHA-256 is `8cc5911e528d0555ee89fe63f0e30b8a3eac4a32e3e4237ee9b00a38107a7d1b`.

The fresh `check_counting.py` independently computes primitive scales from gcds of the original integer coordinate formulas, not from an imported prior checker. It compares shell counts and cumulative counts, verifies the digital identities and exact subsequence formulas, and checks the inverse block endpoints. Its finite results in `checks.json` supplement but do not replace the proofs.

No earlier packet is edited; no author/upstream program, counter interpreter, physical simulator, saved schedule, or proof-assistant execution is used. No OEIS identification, resolved external conjecture, priority, minimality, new halting result, or new universality claim is made. Counting all encoded initializations must not be substituted for counting halting inputs or Diophantine witness tuples.
