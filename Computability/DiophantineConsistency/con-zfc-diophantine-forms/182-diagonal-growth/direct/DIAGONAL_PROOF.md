# A smaller range-free direct quartic by reusing the growth index as its base

Prepared for the ProveIt research package, 25 October 2026.

## 1. Exact claim and comparison

Let `Q214` be the integer polynomial specified by
`diagonal214/equation.json`: it is the sum of the squares of its 153 literal
quadratic residuals in 214 independently unrestricted integer variables.
Its fully collected expansion is supplied separately. Its measured degree is
4, its support has 5,656 monomials, its coefficient height is 219,813, and its
maximum residual coefficient is 464. There are 1,040 residual monomials.

Relative to the identified ordinary Pell and C222 calibration theorems, the
argument below is formalizable in ZFC and proves

    ZFC proves: (there is no integer zero of Q214) iff Con(ZFC).

It does not prove that Q214 has no zero. No consistency assumption is used in
proving the equivalence. No new end-to-end proof-assistant formalization is
claimed. The semantic replacement preserves existence of a zero through the
common finite-refutation interpretation. It does NOT assert a bijection of
the old and new complete zero sets or equality of their polynomials.

The precise parent is source 173's principal P215 at repository commit
`02a78a08603cbae248c19c23a75907c6c6bd6443`, path
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/173-crt-index-anchor-215/equations/principal/equation.json`.
Its original bytes have SHA-256
`8d919a1e5d6a802765b6d010c0140fb1d83c3d36d211b209b7a8d2fb3f3fb6f6`.

| Equation | Integer variables | Rows | Degree | Monomials | Height |
|---|---:|---:|---:|---:|---:|
| Source173 P215 | 215 | 154 | 4 | 5,660 | 91,679 |
| Source173 P214 companion | 214 | 153 | 4 | 5,486 | 1,099,511,627,852 |
| New Q214 | 214 | 153 | 4 | 5,656 | 219,813 |

Q214 removes one variable and one residual relative to P215 while increasing
height. It has the same variable count and degree as the old P214 and reduces
its height by a factor exceeding five million, while increasing support by
170 monomials. Source173's P213 still has fewer variables; its height is
2,417,851,639,242,452,488,945,685. No global minimum or world-priority claim is
made. Diagonal/self-power constructions already appear in source170; the new
contribution here is their use at the range-free C-anchor interface, with the
exact label majorant and fully emitted smaller-coefficient quartic.

## 2. The five changed residuals and one deleted coordinate

All coordinate names in this section refer to the parent principal's final
integral chart, not to a pre-optimization coordinate name. The exact semantic
ports are

    t=x0, beta_code=x1, F=x2, B=x3, y+1=x4,
    C=2*x16, K=x93, W=x131, A=x132,
    E=x139, q_power=x140, D=x181, Y=x182, X=x183+1,
    z=x185.

Thus the retained K-index principal Pell pair is `(X,Y)` and `D=X-A*Y`.
The residuals R126 and R127 remain unchanged and imply exactly these facts:

    1-A*Y-D+x183=0,
    -1+2*D-D^2+2*D*x183+Y^2=0.

Indeed the first says `X=D+A*Y`, and the second is equivalent to
`X^2-(A^2-1)*Y^2=1`. The existing orientation certificate identifies this
pair's canonical index as the actual coordinate K, just as in the parent.

The replacement makes

    c=464,  t=c+z^2,  K=c*t^2,  F=K^K.

The last displayed relation is a mathematical consequence of the retained
Pell power certificate. It is not an operation in the final polynomial.
The actual changed rows are:

| Parent row | New literal residual |
|---|---|
| R96 | `1+K^2-2*K*A+E` |
| R97 | `F-D-K*Y+E*q_power` |
| R128 | `old_R128+t^2-K^2` |
| R130 | `t-464-z^2` |
| R152 | `K-464*t^2` |

Delete old R153 and coordinate x214. The old R152 and R153 were respectively
`x214-t^2` and `K-x214^2`. No retained row uses x214. Every other parent
residual and every retained coordinate is copied literally.

The first two edits change only the growth request's base from t to K. The
nominal index remains K and therefore uses the same principal pair. In the
parent frame, one square was the actual growth base t squared, and another
was the actual index K squared. The frame edit replaces the first by K
squared and keeps the second: every requested base, index and output remains
bounded by the authenticated frame W. Duplicating K in this sum is harmless.

`build_diagonal.py` checks the parent's byte hash, the exact old row interfaces,
the semantic coordinate names, residual degree, and liveness before emitting
the new equation, full expansion, and exact `source_delta.json`. These finite
checks bind the proposed transformation; they do not replace the unbounded
argument below.

## 3. A source-specific bound on all local labels

The arithmetic source is the original square-shell C222 code, not a new
logical calculus. Its four constructors are

    I(a,b)=2*((a+b)^2+a),       M(a,b)=I(a,b)+1,
    Acode(a,b)=2*((a+b)^2+3*a+4*b+3),   Ecode(a,b)=Acode(a,b)+1.

Their coefficients are nonnegative. The nine source axiom expressions and
the additional labels `a,b,I(a,b),Acode(a,b),1` are unchanged. Let J be their
sum as a mathematical polynomial in the four natural local parameters.
It need not be introduced as a coordinate or as a range request.

The independently supplied `../majorant/check_label_majorant.py` binds
the following finite facts to the authentic 2,955-byte `shell_source.py`,
whose SHA-256 is
`59c68a354fe5cdbc04bde33720080db2436cb51ae25e3485ac5ae45ff4230199`:

* every coefficient of J is nonnegative;
* its total degree is D0=524,288;
* the exact diagonal value J(464,464,464,464) has bit length 5,692,913;
* `464^645888` has bit length 5,721,264.

Consequently, with d=645,888=3*464^2,

    J(464,464,464,464) < 2^5692913 < 2^5721263 <= 464^d.

No floating-point logarithm or approximate comparison is used. The checker
provides exact/dyadic arithmetic and the source hash; the mathematical
extension of that one-point bound is as follows.

For any polynomial P with nonnegative coefficients and total degree at most
D0, and t>=c>0, each monomial gives

    P(t,t,t,t) <= P(c,c,c,c)*(t/c)^D0.

Apply this to J with c=464. Since d>=D0 and t>=464,

    J(t,t,t,t) < c^d*(t/c)^D0 <= t^d.

The retained strict range requests give `0<=a,b,c_local,d_local<t` at every
decoded local row. By coefficient nonnegativity every local formula label
is less than `L=t^d`. This includes all possible conclusions and premises.
Truth has label zero and is treated as a unit in the multiplicative encoding.

## 4. Why the new growth is sufficient

For integers t>=c>=3, the inequality `c^t>=t^c` has a direct induction
proof. At t=c it is equality. Suppose `c^n>=n^c` for an integer n>=c.
The finite binomial estimate gives

    (1+1/n)^c <= (1+1/c)^c
                 = sum_(j=0)^c binom(c,j)/c^j
                <= sum_(j=0)^c 1/j! < 3 <= c.

For the strict bound, use `j!>=2^(j-1)` for j>=2 and the finite geometric
sum: `sum_(j=0)^c 1/j! <= 3-2^(1-c) < 3`. Multiplication by n^c now gives

    (n+1)^c < c*n^c <= c*c^n = c^(n+1),

which is exactly the induction step. This proves `c^t>=t^c` for every
integer t>=c without logarithms, real roots, or an infinite-series argument.

With c=464 and K=c*t^2, the new self-power satisfies

    F=K^K
     = c^(c*t^2) * t^(2*c*t^2)
     = (c^t)^(c*t) * t^(2*c*t^2)
     >= t^(c^2*t+2*c*t^2)
     >= t^(3*c^2*t)
     = (t^d)^t = L^t.

All exponents in this proof are natural integers. The construction therefore
meets exactly the growth interface needed by source173's label-separation
theorem, with substantially smaller literal quadratic coefficients.

## 5. Soundness in the required order

Assume an arbitrary integer tuple is a zero of Q214. Since Q214 is a sum of
integer squares, every residual vanishes. The new horizon row gives
`t>=464`, and the new growth-index row gives `K=464*t^2>0`. The frame still
contains all actual base, index and output atoms. Its unchanged Pell-frame
rows give the same large nondegenerate signed center A; the unchanged
C-anchor cap, comparison and orientation argument recovers every canonical
principal pair, including the K pair. This argument uses the authenticated
frame and anchor cap before semantic signs of CRT representatives are
recovered. It does not assume the desired power relation in advance.

The two edited power rows are precisely the parent's singleton power
certificate for base K and index K. Both are already positive, and the
frame bounds K. Hence they force `F=K^K`. Since `K=464*t^2` is positive
and even, F is positive and even before the remaining sign bootstrap is
used. Also C=2*x16 is even without any assumption on its sign. The retained
divisibility `B | C+F+1` therefore has an odd right-hand side, forcing B to
be nonzero and odd. These are precisely the parity and nonvanishing facts
needed by the parent's acyclic sign bootstrap. The unchanged singleton
and pooled requests recover all other required powers, and the beta sign
and range/digit arguments then apply in their original order.

For completeness of the input interface, the preserved conditions include:

1. all nine remaining independent local-column range requests, including
   the encoded row-index range;
2. the two beta endpoint congruences and the same local Horn polynomial;
3. every-prime binomial-CRT coverage and `B | C+F+1`;
4. all singleton/pooled power divisibility and error budgets;
5. the same principal norms, cap, auxiliary comparison and orientation;
6. every actual requested atom in the frame, including growth base and index K.

Only the already-deleted derived-label range of source173 remains absent.
Section3 supplies its needed label bound. The unchanged local-polynomial
majorant is valid for t>=16 and F sufficiently large. Here t>=464 and
`F>=t^(d*t)` are stronger hypotheses. In particular the beta bootstrap gives
`x>=2+(t+1)*y`, `y>=F`; hence x is more than sufficient for the parent's
exact local bound `Local<2^x`.

There is no new assumption that t is even. If Lambda=lcm(1,...,t), then for
every positive integer t,

    Lambda^2 <= (t!)^2 <= t^(2*t) <= F,

because d>=2. This proves the generalized binomial-CRT radius condition
uniformly for odd and even horizons. Any old sharper estimate that was
stated only for even t is unnecessary here.

The decoded t local rows satisfy the same weighted updates
`S_(i+1)*(1+F*v_i)=S_i*(1+F*p_i)*(1+F*q_i)`. The initial and terminal
conditions yield

    product_i(1+F*v_i) = (1+F)*product_i(1+F*p_i)*(1+F*q_i).

All positive labels are at most L, the left has at most t nonunit factors,
and the right at most 2t+1. Since `F>=L^t`, the parent's sharp product
separation lemma recovers equality of the two label multisets, including
the target label1. The single-conclusion Horn-flow closure argument then
extracts a finite C222 refutation even when the selected rule multiset
contains cycles. Thus every integer zero yields a finite refutation.

## 6. Completeness and the changed parity argument

Start with an arbitrary finite C222 refutation. Choose an integer z so large
that `t=464+z^2` exceeds its number of local steps and every independent
source parameter; pad with legitimate truth steps as in the parent. Set
`K=464*t^2`, `F=K^K`. The label and growth bounds just proved hold.

Because `464=16*29`, K is even regardless of t and

    v2(K)=4+2*v2(t),
    v2(F)=K*v2(K)>=4*K>2*t.

Let O be the odd part of t!. Choose a sufficiently large positive odd
multiple u of O and set `y=F*u`. Then t! divides y, y>F, and y can be made
larger than every genuine pending-multiset state. It has the required
literal shape `y=F*(2*w+1)`. The beta moduli `1+(i+1)*y` are odd and
pairwise coprime; ordinary CRT gives a sufficiently large positive beta
code x. This is the only replacement needed for the old horizon-multiple-
of-four argument.

The generalized binomial source sets `B=binom(F+t,t)` and `N=B^x`.
For each 1<=i<=t, `v2(F)>floor(log2(t))` gives `v2(F+i)=v2(i)`, so B is
odd. Construct the same compatible local-column CRT residue classes at
every prime of B. Their common modulus N^2 is odd. Choose the eight
ordinary representatives first; then choose C even, in its prescribed
class modulo N^2, and larger than every other nominal index, including K.
This remains a cofinal arithmetic progression. Only afterwards choose
the self-sized radix and all subsequent power outputs, then construct
the actual frame, its canonical center and every principal Pell pair.

The unchanged cofinal-C proof supplies the cap, orientation and odd
auxiliary witnesses. The singleton growth request now uses canonical
base K and index K and has exact output F by construction; it therefore
has the required integral quotient. All retained range, pooled and local
witnesses are supplied exactly as in the parent. Set the new growth-index
wire to K and omit the old private t-squared wire. This constructs a
complete integer zero of Q214.

## 7. Logical calibration and formalization boundary

Sections5 and6 prove arithmetic existence of a zero iff existence of a
finite refutation in the unchanged numerical calculus C222. The inherited
logical endpoints are `KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`, at the pinned
repository source. No Turing-machine simulation or universal-polynomial
specialization is introduced by this candidate.

The argument uses finite syntax, integer polynomial identities, elementary
integer inequalities, ordinary finite CRT and the explicitly inherited
Pell representation and logical calibration. They are used uniformly over
the arithmetic of ZFC, not merely over externally standard numerals.
Their formalizability composes to the stated ZFC-provable equivalence.
The new source arithmetic and its object-language composition have not
been supplied as a new checked Lean or Rocq derivation. Finite coefficient
or sample checks should never be described as establishing those unbounded
theorems.

## 8. Preserved source references

The parent ordinary dependencies, available at the stated commit under
source173, are:

* `proofs/LABEL_SEPARATION_WITHOUT_DERIVED_RANGE.md`, for sharp product
  separation, local-size and every-prime completeness interfaces;
* `proofs/C_ANCHOR_THEOREM.md`, for noncircular anchor classification,
  orientation, cofinal CRT choice and auxiliary witnesses;
* `proofs/ORDINARY_PROOF_DEPENDENCY_BOUNDARY.md`, for the inherited
  arithmetic/logical boundary;
* `code/check_constructor_depth.py` and the pinned square-shell source,
  for source-polynomial identification (the current sharper certificate
  changes the numerical majorant, not these formulas).

The existing diagonal source is
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/170-quotient-carriers/direct/diagonal_pool/inputs/DIAGONAL_SOURCE_PROOF.md`.
The present report explicitly credits that prior idea and claims only its
new, verified transfer and measured tradeoff.
