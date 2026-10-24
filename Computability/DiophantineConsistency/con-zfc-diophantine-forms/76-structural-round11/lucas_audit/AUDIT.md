# Independent audit: one-factor Lucas saturation

## Verdict

The proposed ten-unrestricted-integer equation passes this independent mathematical and literal-artifact audit, with the explicitly retained source/Pell interfaces. It has481 live binary operations and exact total degree1,248,364. The preceding481-operation polynomial had degree1,576,864. This is a degree reduction, not a variable-count or operation-count improvement. No proof-assistant certificate or global minimality claim is made.

The genuinely new step is to replace the square C^4 D^2 xi^2 by C^4 D xi^2 in F and G, without making the same replacement in the interpolation modulus. The square root d of D exists only in the correctness proof and is not a new quantified coordinate. The proof must use the arithmetic guard to exclude C=±1. Omitting this step is false, as the counterexample below demonstrates.

## 1. Literal definitions audited

Let A be an even integer polynomial and put

    D=(A^2−4)C^2+4,
    F=4(A^2−4)C^4 D xi^2+1,
    G=(A/2−1)(F−1)−1,
    Omega=16C^2Dxi,
    H=C+F(B−C+Omega y),
    I=(G^2−1)H^2+1.

Here A/2 is already a supplied polynomial, not a division operation. The audit independently checked the literal alternative expression G=2(A+2)(A−2)^2C^4Dxi^2−1, so the half-A implementation and direct evaluator agree.

Compared with the authenticated preceding archive, the first460 DAG nodes (through D), all31 source weights, all22 targets, kernel polynomials and all12 actual fixed coefficients are unchanged. The new tail is checked against direct scalar formulas, not by importing the producer or its evaluator.

## 2. Reliability and exceptional indices

Assume |A|>2, A even, C odd with |C|>1, xi≠0, and B odd with1<B<|A|/2−1. All of D,F,I are positive. For positive A, A/2−1≥1 and F−1 is sufficiently large, giving G>1; for negative A, G<−1. The following exact identities give pairwise coprimality:

    F=1 (mod D), G=−1 (mod D), I=1 (mod D),
    2G=(A−2)F−A, 4I=D (mod F).

F is odd. Therefore DFI square implies that D,F,I are separately squares. Write d=√D>0. The standard Pell classification produces

    C=u_s(A), 4C^2 d xi=u_mu(A), H=u_t(2G).

A useful simplification is that n=|mu|>3 does not need a bound on u_3. Since C≠0, D≥A^2 and d≥|A|. Hence |u_mu(A)|≥4|A|>|u_2(A)|. This Lucas value is even, so mu is even and nonzero. Monotonicity of |u_n(A)| then gives n≥4. Also F=(v_n(A)/2)^2. C,H,s,t are odd.

Apply the classical index-separation implication to C=H modulo F and 2G=−A modulo F: s=±t modulo2n. The square divisibility C^2|u_n(A) and oddness of C give C|n by Lucas valuation. The new congruences are valid because

    (F−1)/(Omega xi)=(A^2−4)C^2/4,
    (2G+2)/(Omega xi)=(A−2)(A^2−4)C^2/4.

Thus H=B and u_t(2G)=t modulo Omega, yielding s=±B modulo2C. Because |C|>1, the index s is not±1. Lucas growth yields |C|≥|A|, |s|≤|C| and B<|C|, so the congruence forces s=±B exactly. On the actual slice A=0(mod3), B=3(mod4), C=−1(mod3), recurrence modulo3 selects s=B.

The external arithmetic inputs just used are classical Pell classification, Lucas index separation and rank valuation; precise statements are recorded in Lemmas2.1–2.4 and Corollary2.1 of Sun's paper [1]. They are assumptions of the inherited mathematical interfaces, not newly checked Lean facts in this audit.

## 3. Why the full equation supplies |C|>1

This must precede the final index collapse. The unchanged norm merger first separates the two square radicands using their distinct residues modulo3, with no positivity premise. It gives the positive-square source scale and Delta>0. The source guard then gives g≥1, K≠0, l≠0, and Y>256. With L=lY,

    Delta>0 => 4g(C−KL)^2<K^2 => |C−KL|<|K|/2.

Consequently

    |C|>|K|(|L|−1/2)≥Y−1/2>1.

There is no circular appeal to the Lucas equation here. The guard and source scale have already been recovered from the separate first radicand. This explicitly replaces the old exceptional-index argument, which depended on the extra D factor that has now been removed.

All other signed-bootstrap cases were checked against the full proof: Sigma=0 is excluded by the root-free homogeneous quintic; distinct radicands exclude zero rational norm root; rational square roots of integers are integral; the two coprime guard factors and residue1 modulo3 exclude negative signed squares; Delta>0 forces positive g and nonzero K; l=0 would give Q=1−K^2≤0. The unchanged source then supplies the required X,Y and B-range bounds.

## 4. Full residue interpolation, not just existence

For canonical A>2, odd B>0 and C=u_B(A), set d=v_B(A)>0. For any positive prescribed divisor N choose a positive matrix period n modulo4NC^2d. Define xi=u_n(A)/(4C^2d). It is positive and divisible by N. Put r=v_n(A)/2. Then F=r^2, r is odd, and

    Omega=4d u_n(A).

The standard matrix argument supplies a period lambda=4nr modulo F. Crucially, let q=lambda/gcd(lambda,Omega). If p|xi, then p∤r since F=1 modulo xi. Lucas valuations, including the even-parameter2-adic case, give

    ord_p(lambda)=ord_p(4n)≤ord_p(4u_n(A))≤ord_p(Omega).

Therefore gcd(q,xi)=1. For any desired residue c modulo xi choose positive L divisible by q with L=c modulo xi and set j=B+Omega L. It is odd. With H0=u_j(2G), periodicity gives H0=C modulo F, while reduction modulo Omega gives H0=B. The quotient

    y=(H0−C−(B−C)F)/(Omega F)

is integral. Using the two quotient identities above modulo Omega xi gives y=L=c modulo xi. The Lucas identity makes I square.

This proves the stronger interpolation property required by the quintic divisibility merger. Merely substituting a multiple into the previous existential Lucas certificate would not prove this residue coverage. Retaining the full D inside Omega is essential to the displayed argument: its extra factor d only improves valuation absorption.

Completeness of the full equation now follows by the inherited canonical source, the positive nonsquare Pell parameter(9Delta−3)r, the choice N=z, and a quintic-root residue class modulo xi. Both square radicands and divisibility hold, and the final integer m is supplied by their square roots.

## 5. A concrete countercontrol if |C|>1 is dropped

The shortened standalone certificate is not reliable under just the old fixed congruence slice. Take

    A=72, B=31, C=−1, n=8,
    xi=34,788,219,551,
    F=129,992,755,125,709,062,769,394,580,481,
    G=4,549,746,429,399,817,196,928,810,316,799,
    Omega=2,885,474,082,438,144,
    lambda=11,537,442,578,350,112.

Here xi=u_8(72)/(4·72), d=72, F=(v_8(72)/2)^2 and gcd(lambda,Omega)=32. The integer

    j=1,038,737,707,386,980,908,103,831,374,879

satisfies j=−1 modulo lambda and j=31 modulo Omega. Define H=u_j(2G) and y by the quotient in section4. The modular identities show y is an integer. D,F,I are squares, yet C≠u_31(72). All of A=0(mod3), B=3(mod4), C=−1(mod3) and1<B<|A|/2−1 hold.

This is not a counterexample to the full consistency equation: its Delta/source bounds force |C|>1. It is a precise diagnostic preventing an invalid weakening of the new lemma. The checker validates the displayed finite constants and congruences by binary matrix powering; it does not try to print the enormous H.

## 6. Exact degree and checks

Let a=deg A=16424. Independent DAG propagation gives

    deg D=2a+2, deg F=4a+10, deg G=5a+10,
    deg Omega=2a+6, deg H=6a+17, deg I=22a+54,
    deg(DFI)=28a+66, deg Sigma=5a+2.

The unique dominant final term is Sigma^4(DFI)^2, of degree76a+140=1,248,364. The other norm term has degree1,083,765. To certify attainment with the actual numeral coefficients, the checker evaluates the top homogeneous component after three separately specified linear substitutions modulo distinct primes. Its nonzero leading coefficients are480742559,955363917 and193742485, modulo1000000007,1000000009 and998244353 respectively. One already suffices to establish the lower bound; the receipt includes the slopes.

`check_independent.py` checks:
- authenticated inherited baseline files and12 coefficient payload hashes, plus exact reconstruction of every fixed coefficient from the four actual source ports;
-460 unchanged prefix nodes, exact data identity and full liveness;
-481 operations and exact degree using actual numeral leaves;
-480 independently evaluated signed source-prefix and tail cases, including zero-coordinate cases;
-1,080 signed local parameter cases for positivity, coprimality and congruences;
-12 finite matrix-period interpolation instances with three prescribed residue classes each;
-the exceptional-index countercontrol above.

Normal and optimized Python results agree. These checks supplement the mathematical proof; they do not establish the unbounded source calibration or a new proof-assistant endpoint.

## Reference

[1] Z.-W. Sun, *Ten unknowns for Hilbert's tenth problem over the integers*, arXiv:2609.01594v1, especially the arithmetic inputs in section2 and the comparison certificate/interpolation in sections3–4. https://arxiv.org/html/2609.01594v1

The modified definitions and their proof above are the subject of this audit; the original theorem is not silently applied to changed formulas.


## Combined H1868 construction: independent extension

The recommended combined literal is `../lucas_h1868/integer10.json`, frozen at SHA-256
`08b594182e27069cdba559b8f1661cf48cc13b06892580816e3d7b2353227bdc`.
It has 480 live binary operations (300 multiplications, 155 additions, 25 subtractions)
and exact total degree 1,245,324. Its source parameter has degree 16,384, giving
76*16,384+140. The unchanged finalizer proof in this audit applies to it.

The H1868 source layout changes target positions but retains all source variables,
weights, residuals, coefficient ports and extraction logic. Its finite extraction
certificate is separate, under `../packing/certified`; this audit does not claim
that the target reassignment follows merely from the old prefix being identical.
Instead the checker reads the new kernel and code data, reconstructs all fixed
coefficient leaves as exact integers from the four actual source ports, and
independently evaluates the sparse prefix directly. It then compares every
named prefix register and the entire modified tail with the literal DAG in
480 signed modular cases, including zero-coordinate controls.

For the combined circuit, the nonzero top-degree coefficients are
[(1000000007, 376403647), (1000000009, 111011115), (998244353, 553128976)]
where each pair is (prime, leading coefficient). The receipt contains every
linear-substitution slope. These are certificates of degree attainment with the
actual fixed numerals, not with formal coefficient placeholders.

Run the independent combined check with
`python check_independent.py --h1868` from this directory. It imports no producer
or upstream module. The 1,080 signed local tests, 12 CRT instances and exceptional
index countercontrol are repeated for this receipt as well. All finite checks
supplement the unbounded mathematical proof, not a new kernel-certified endpoint.

The combined normal and optimized (`python -O`) runs produce byte-identical receipts.
