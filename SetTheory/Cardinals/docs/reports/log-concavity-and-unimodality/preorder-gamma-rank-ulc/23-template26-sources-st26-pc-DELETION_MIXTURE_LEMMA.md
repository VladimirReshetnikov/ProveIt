# Deletion-mixture lemma for the three-core single-arc family

Status: exact algebraic proof package prepared, separate from the frozen degree-four archive. The ten new quartic identities pass a fresh symbolic verifier. Independent audit and structural compression remain separate tasks.

## Statement

Let the core be three sinks 0,1,2 with internal arc 2→0, and let independent exterior tail types 1,2,3,5,7 have nonnegative integer populations m=(a,b,c,d,e). Write Q(m)=(1,A,B,T), where

A=1+a+b+2c+2d+3e,

B=ab+ac+ad+2ae+bc+2bd+2be+3cd+3ce+3de+binom(c,2)+binom(d,2)+3binom(e,2)+b+c+e,

T=b((d+e)(a+c)+binom(d+e,2))+a(cd+ce+de+binom(e,2))+binom(c+d+e,3)-binom(c,3)-binom(d,3).

Let Q_*=Q(m), and let Q_i=Q(m-e_i) for any type i with m_i>0. Every nonnegative linear combination R=sum_i w_i Q_i (including Q_*) satisfies its order-three last Newton inequality

R_2² >= 3 R_1 R_3.

The principal result of Sections 1–4 is this last inequality. Section 6 separately proves the first order-three inequality R_1²>=3R_0R_2. Thus R is ULC with respect to order three. If its surviving degree is two, the stronger actual-degree normalization R_1²>=4R_0R_2 is not asserted by this package. The constant coefficient of R need not be 1.

## 1. Two-point reduction

For any finite list of triples (A_i,B_i,T_i) with A_i>0, nonnegative mixtures satisfy B²>=3AT if and only if every two-triple mixture does.

Indeed, normalize a nonzero mixture by A. Its point (B/A,T/A) lies in the convex hull of the normalized points p_i=(B_i/A_i,T_i/A_i). At any fixed horizontal coordinate x, the greatest attainable vertical coordinate in this finite convex hull is attained by a convex combination supported on at most two vertices. One elementary proof is to maximize sum_i lambda_i y_i subject to sum_i lambda_i=1, sum_i lambda_i x_i=x, lambda_i>=0; a basic feasible optimum uses at most two variables. If every two-point segment lies on or below y=x²/3, so does the whole hull. The converse is immediate. Zero total weight is trivial.

All triples here have A_i>=1 because the fixed internal arc remains present.

## 2. Undeleted/deleted pairs

For a marked physical exterior vertex of type i, its vertex activity t gives exactly

Q(t)=t Q_*+(1-t)Q_i, 0<=t<=1,

because each support uses that physical vertex either once or not at all. This changes the activity of one physical vertex while every other physical vertex retains activity 1. It is not the substitution of a fractional number into the population binomial formulas; the two operations generally differ for types c,d,e. The approved vertex-weighted degree-at-most-three theorem gives B(t)²>=3A(t)T(t). If its surviving degree is below three, then T(t)=0 and this particular last order-three inequality is trivial. Scaling covers every nonnegative two-term combination of Q_* and Q_i.

Dependency: /workspace/shared/weighted-preorder-gamma/VERTEX_WEIGHTED_DEGREE3_THEOREM.md, together with the separately approved audit receipt in weighted-vertex-seven-independent-audit/approval_receipt.json. No independent-edge-activity theorem is invoked.

## 3. Distinct deleted types

For each i<j among the five types, define

C_ij=2 B_i B_j-3(A_i T_j+A_j T_i).

The accompanying certificate file proves C_ij>=0 on its integer population domain. To eliminate the required lower bounds m_i,m_j>=1, the polynomial and certificate use residual variables x>=0 with m=x+e_i+e_j.

Each identity has the form

C_ij(x+e_i+e_j)=sum_l q_l binom(x,alpha_l) f_l(x)² + sum_beta r_beta binom(x,beta),

where q_l,r_beta are positive rational numbers, alpha_l,beta are nonnegative exponent vectors, binom(x,alpha)=product_k binom(x_k,alpha_k), and f_l is an explicitly listed polynomial in the same binomial basis. Every summand is nonnegative at nonnegative integer x.

The diagonal gaps G_i=B_i²-3A_iT_i are nonnegative by the degree-at-most-three theorem, so

G(uQ_i+vQ_j)=u²G_i+uv C_ij+v²G_j>=0.

The ten certificates contain respectively 15,21,18,22,24,19,21,18,19,19 squares. This is an exact finite proof, not yet a compact structural square identity.

## 4. Conclusion and audit files

Sections 2 and 3 check all two-point segments, and Section 1 proves the claimed arbitrary-mixture inequality.

- distinct_deletion_cross_certificates.json: all ten exact identities
- verify_distinct_deletion_cross.py: standalone exact SymPy verifier, directly rebuilding the A,B,T formulas and all shifts; it uses no numerical optimization or legacy certificate imports
- verify_distinct_deletion_cross.log: all ten PASS results

The verifier confirms each identity coefficientwise in ordinary polynomials and separately checks positivity of every rational square weight and binomial-remainder coefficient. No authoritative or frozen artifact was modified.

## 5. Why the initially stronger condition was unnecessary

The cross gap for Q_* and Q_b can be negative. At (a,b,c,d,e)=(1,1,0,1,0), Q_*=(1,5,5,1), Q_b=(1,4,1,0), and C_*b=-2. Nevertheless the binary last gap is 10u²-2uv+v²=(v-u)²+9u²>=0. Thus demanding all fifteen cross coefficients be nonnegative is strictly stronger than the mixture lemma.


## 6. First order-three Newton inequality: a common three-square identity

The first inequality is R_1²>=3R_0R_2. For a distinct-deletion pair its cross coefficient is

F_ij=2A_iA_j-3(B_i+B_j).

As before, use shifted residual populations x=(a,b,c,d,e)>=0 with m=x+e_i+e_j. Put

S=(a-b+1)²+(b-2d-2)²+(c-d)²+a²+4c²+9e²+2a(c+d)+2bc+6e(c+d).

Then each F_ij equals S plus an ordinary linear polynomial. The following rows list its coefficients in the order (a,b,c,d,e,1), with type indices 0,1,2,3,4 corresponding to populations a,b,c,d,e:

- (0,1): (3,5,7,2,15,0)
- (0,2): (5,4,11,3,18,4)
- (0,3): (5,1,5,9,18,7)
- (0,4): (4,3,9,7,24,8)
- (1,2): (2,7,11,0,18,1)
- (1,3): (2,4,5,6,18,4)
- (1,4): (1,6,9,4,24,5)
- (2,3): (4,3,9,7,21,10)
- (2,4): (3,5,13,5,27,13)
- (3,4): (3,2,7,11,27,16)

Every displayed term is nonnegative, even for real residual populations. These identities are independently expanded and checked by verify_first_gap_cross.py; its output is verify_first_gap_cross.log.

Each diagonal first gap is nonnegative by the degree-at-most-three theorem. Every Q_*/Q_i segment is handled by the single-physical-vertex activity argument from Section 2. Hence every two-point mixture satisfies the first gap. Apply the same two-point reduction after normalizing by R_0, now with points (A_i,B_i) and safe region y<=x²/3. It follows that every nonnegative mixture satisfies R_1²>=3R_0R_2.
