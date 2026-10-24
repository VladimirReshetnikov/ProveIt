# A six-coordinate global tiling certificate

## Status and scope

This is a proved arithmetic theorem for every fixed finite set of Wang tiles. It is a new route in this project, not a claim of historical priority for arithmetizing tilings or using Lucas' theorem. Unlike the preceding bounded-family CRT approach, its number of exposed coordinates and special-function calls is independent of both the rectangle size and the number of tile types. Tile-set size is paid for in fixed polynomial degrees and coefficients.

The theorem does **not** by itself give a calibrated polynomial for Con(ZFC). A separate generic TM-to-tiles compiler is now supplied and instantiated as a literal 7,782-tile set for the pinned K215 machine; see TM_COMPILER_PROOF.md. A direct-checker tile instantiation, compiled power/binomial graph polynomials, and the complete internal ZFC interpretation are still not supplied. These omissions are explicit interfaces, not notation silently treated as polynomial.

## 1. Input: a strict-boundary tile set

Fix k>=1 tile types numbered 0,...,k-1. Tile t has nonnegative integer edge colors w_t,e_t,n_t,s_t. Color 0 is the boundary color. A strict-boundary rectangular tiling has positive width w and height h, matches adjacent edges, and has color 0 on an edge if and only if that edge lies on the outer boundary. Tiles are not rotated. Width or height one is allowed; a tile can have both opposite edges zero.

Choose a power of two C strictly greater than k and every edge color. Set A0=2C^2. Choose any power of two D>=32kA0. These are fixed integer coefficients, not variables.

## 2. Only six exposed natural coordinates

The coordinates are a,b,Q,G,Z,r. Define the following ordinary polynomial expressions:

    P = 1+(C-1)G,
    H = A0 P,
    R = D P^3,
    B = (D/2) P^3,
    L = R^(2k).

Require exactly two variable-power graphs:

    Q = C^(a+1),             P = Q^(b+1).

Thus, in the proof only, w=a+1, h=b+1 and N=wh, so P=C^N and G=(P-1)/(C-1). All subsequent displayed exponents, such as 2k, are fixed integers determined by the fixed tile set.

For a formal vector x=(x_0,...,x_(k-1)), put U=sum x_t and define seven linear residuals ell_j(x)=sum_t a_jt x_t+c_j:

1. U-G.
2. (Q-1) sum_(w_t=0) x_t -(P-1).
3. C sum_(e_t=0) x_t - Q sum_(w_t=0) x_t.
4. C sum_t e_t x_t - sum_t w_t x_t.
5. Q sum_t s_t x_t - sum_t n_t x_t.
6. (C-1) sum_(n_t=0) x_t -(Q-1).
7. Q sum_(s_t=0) x_t - P sum_(n_t=0) x_t.

The x_t are NOT variables in the certificate. They name digits recovered only in the proof. Each coefficient a_jt is a fixed ordinary polynomial in Q,G, and each c_j is one of -G, -(P-1), 0, -(Q-1).

Define fixed polynomial convolution filters and outputs:

    K_j = sum_(t=0)^(k-1) (H+a_jt) R^(k-1-t),
    F_j = K_j Z + (B-HG+c_j) R^(k-1).

Define masks and the final packed pair:

    M0 = G sum_(t=0)^(k-1) R^t,
    M1 = R^(2k-1)-1 -(R-1-B)R^(k-1),
    A = M0 + M1 sum_(j=1)^7 L^j,
    Y = Z + sum_(j=1)^7 F_j L^j.

Require a single total-binomial graph:

    binom(A,Y) = 2r+1.

The convention is binom(A,Y)=0 for Y>A. The complete six-coordinate certificate consists of these three graph assertions and no hidden bounded quantifier.

## 3. Theorem

There exist natural a,b,Q,G,Z,r satisfying this certificate if and only if the fixed tile set has a strict-boundary rectangular tiling.

More precisely, with the first two power graphs fixed to width w and height h, the possible Z are in bijection with the strict-boundary tilings of that exact rectangle; r is then determined by the binomial value.

## 4. Proof: binary subset and the no-carry bootstrap

For natural u,v, binom(u,v) is odd exactly when every 1-bit of v is also a 1-bit of u. This follows directly in F_2[X] from (1+X)^u=product_(i:u_i=1)(1+X^(2^i)). Denote the relation by v subset_bits u.

Under the two power graphs, P>=Q>=C>=2 and 0<G<P. Every coefficient satisfies |a_jt|<=C^2P=H/2 and |c_j|<=P. Hence H+a_jt>=H/2>=1, and

    B-HG+c_j >= B-HP-P > 0.

The last strict inequality follows from B=(D/2)P^3 and D>=32kA0. Thus every F_j is nonnegative for every natural Z; moreover F_7>=Z.

Since R is a power of two and G<R, we have M0<R^k<L. The expression M1 is the base-R word of length 2k-1 whose digits are all R-1 except digit k-1, which is B=R/2. Consequently 0<=M1<L and 0<=A<L^8.

Suppose Y subset_bits A. Then Y<=A<L^8. Since all packed summands are nonnegative and F_7>=Z,

    Z L^7 <= F_7 L^7 <= Y < L^8,

so Z<L. Reducing Y modulo L now gives exactly Z. The bottom L-block of A is M0. Therefore Z subset_bits M0.

This is the crucial bootstrap: no advance range assertion for Z, no k digit coordinates and no quotient/remainder witnesses are needed. It would be invalid to infer the bottom-block property without first proving Z<L; the top convolution block supplies that proof.

Write Z=sum_t x_t R^t. Since Z subset_bits M0, all its digits beyond k-1 vanish and every x_t subset_bits G. In particular 0<=x_t<=G<P.

Consider F_j as a formal base-R convolution. Every noncentral coefficient is at most 2kHG<2kA0P^2<R/8. Its central coefficient is

    d_j = B + ell_j(x) + H(U-G).

Directly from the nonnegative convolution and its offset,

    B-HG-P <= d_j <= B+2kHG+P.

The same choice D>=32kA0 gives 0<d_j<R. Hence no coefficient carries occur anywhere, and F_j<R^(2k-1)<L. All eight packed L-blocks therefore separate exactly. The seven conditions F_j subset_bits M1 say that each d_j is a binary subset of the single-bit number B. Since d_j>0, each d_j=B.

For j=1 this is (H+1)(U-G)=0, so U=G. With U=G, every remaining central equality is exactly ell_j(x)=0.

Conversely, if x_t subset_bits G and ell_j(x)=0 for all j, the same no-carry calculation gives F_j subset_bits M1 and Z subset_bits M0, hence Y subset_bits A. Thus the packed test is exactly equivalent to the seven linear identities plus the digit-subset conditions.

## 5. Proof: from words to the whole rectangle

Since P=C^N, G=1+C+...+C^(N-1). A binary subset of G has base-C digits only 0 or 1. Because k<C, adding k such words makes no base-C carry. The identity U=G therefore says that at every cell exactly one tile mask x_t has digit 1. This reconstructs the entire rectangle.

The second residual fixes the west-zero mask to

    (P-1)/(Q-1)=1+Q+...+Q^(h-1),

which is exactly the first column. The third fixes the east-zero mask to (Q/C) times that mask, exactly the last column. The sixth fixes the north-zero mask to (Q-1)/(C-1), exactly the first row; the seventh fixes the south-zero mask to (P/Q) times the first-row mask, exactly the last row.

With one tile per cell and colors<C, the edge-color words have genuine base-C digits equal to the corresponding edge colors, with no carries. Residual 4 states C E=W: every east color equals the next west color in the flattened word. At a row join both colors are zero by the fixed side masks; all actual within-row matches are therefore exact. Residual 5 states Q S=N: all vertically adjacent edge colors match, with the prescribed zero top and bottom boundaries. This proves soundness.

For completeness, encode each actual tile occurrence by x_t=sum C^i over its occupied cells and set Z=sum x_t R^t. All seven residuals vanish by the geometry, and every x_t is a binary subset of G. The previous step proves the odd-binomial certificate. No unbounded search, prime selection, CRT or factorial graph is involved in this argument.

## 6. Exact conditional ordinary-polynomial interface

Suppose E(u,v,z;eta)=0 is a selected exact natural graph polynomial for z=u^v with p internal natural witnesses eta, excluding visible inputs and output. Suppose J(u,v,z;xi)=0 is a selected exact graph polynomial for total binomial with b internal witnesses xi. Then the literal ordinary polynomial

    E(C,a+1,Q;eta1)^2
  + E(Q,b+1,1+(C-1)G;eta2)^2
  + J(A,Y,2r+1;xi)^2

has a natural zero exactly when the fixed tile set has a strict-boundary rectangle. It has exactly

    6+2p+b

natural variables under this declared graph interface, independent of k. No numerical values for p or b are claimed. The certificate does not use universal-polynomial parameters, K215 or Jones' universal formula.

With total graph degrees delta_E,delta_J, A has degree at most 48k-3 and Y at most 45k in Q,G,Z. Thus the displayed squared-sum polynomial has degree at most 2 max(delta_E,(48k-3)delta_J). Degree can be high even though the exposed-coordinate count is fixed.

## 7. Binomial-free version: five power graphs and nine coordinates

The remaining binomial graph can itself be eliminated without a factorial graph. For arbitrary natural A,Y, set d=2^(A+1). The digits of (d+1)^A in base d are exactly binom(A,i), since each coefficient is <=2^A<d. Therefore binom(A,Y) is odd exactly when there are natural d,q,s,t with

    d = 2^(A+1),
    s+t+1 = 2^((A+1)Y),
    (s+t+1)(2q+1)+s = (d+1)^A.

Indeed s is the remainder modulo d^Y, is strictly smaller than it, and the quotient is odd. If Y>A the quotient is zero and the certificate has no solution, so the total-binomial convention is preserved.

Replace r by d,q,s,t. Together with the two geometric power calls, the resulting formula contains exactly five power calls, nine exposed natural coordinates and no binomial or factorial graph. Its conditional ordinary-polynomial count is

    9+5p.

Its squared-sum degree is at most 2(93k-3)delta_E. This is a completely exposed power-only interface, not a claim that variable exponentiation is already polynomial.

## 8. Remaining path to the requested consistency polynomial

1. For the independent direct-checker route, supply a literal finite strict-boundary tile set and its computation equivalence. The external 83,281-node primitive-recursive code is not itself that tile set. The separate K215 instantiation now closes the machine-to-tile gap for that pinned machine: TM_COMPILER_PROOF.md proves the generic compiler theorem and K215_TILES.json contains its literal 7,782-tile output.
2. Supply and count a literal exact power graph (and optionally binomial graph), including all auxiliary natural coordinates and any port-expression sharing.
3. Prove the complete arithmetic construction and checker/tile equivalence inside the intended object-language arithmetic of ZFC, over its entire internal natural-number object. Standard-natural correctness alone is not this internal interpretation.
4. Only then compare the resulting degree/count/coefficient budget to the completed existing consistency polynomials. The constant-coordinate interface can conceal substantial degree and coefficient costs; it is not a claimed improvement of the final variable frontier yet.

The supplied executable tests validate arithmetic identities, positive fixtures, malformed masks, every board over small tile sets and decisive negative controls. They are not a Lean formalization or a substitute for these universal proofs.

## Sources and relation to prior methods

The only number-theoretic ingredient beyond elementary positional arithmetic is the binary case of Lucas' theorem, proved above. Reference: R. Meštrović, *Lucas' theorem: its generalizations, extensions and applications (1878–2014)*, https://arxiv.org/abs/1409.3820 . Historical exponential arithmetization should be distinguished from the specific packed-convolution construction here: Yu. Matiyasevich, *A new proof of the theorem on exponential diophantine representation of enumerable sets* (1976/1980), https://www.mathnet.ru/eng/znsl2072 .

## 9. The supplied machine instance admits five exposed coordinates

The generic theorem remains a six-coordinate theorem for arbitrary strict-boundary tile sets. The separately supplied TM compiler has a stronger completeness property: a T-step halting run fits a square of side T+2, because its visited tape span has length at most T+1. The compiler's boundary rule allows this without symmetric padding. TM_COMPILER_PROOF.md gives the complete argument and tests.

For that compiled-machine tile set only, identify b=a. The first two power graphs become Q=C^(a+1) and 1+(C-1)G=Q^(a+1). All packed polynomial expressions remain unchanged. The exposed coordinates are now a,Q,G,Z,r, and the exact conditional counts are 5+2p+b or, after parity extraction, 8+5p. The literal K215 interface DAG uses this square corollary. No claim that arbitrary rectangularly tileable tile sets admit square tilings is made.

## 10. Finer graph-cost interface

Since C is a fixed power of two, write C=2^c with fixed c (c=13 for the literal K215 instance). The two geometric power calls can equivalently be Q=2^(c(a+1)) and P=2^(c(a+1)(b+1)); in the square specialization the second exponent is c(a+1)^2. Of the three parity-extraction calls, the first two already have base 2. Therefore the square power-only interface actually needs four fixed-base-2 graphs and only one general-base graph, namely (d+1)^A.

If a chosen exact fixed-base graph has p_2 internal witnesses and a general-base graph has p_g, the square counts refine to 5+2p_2+b or 8+4p_2+p_g. The earlier uniform count uses p_2=p_g=p and remains valid. No values for these costs are supplied or presumed.
