# A complete positive binary-to-radix16 input recoder

For ordinary positive integers x,z, the relation

    z=spread4(x):=sum_j bit_j(x)*16^j                 (1)

has a fully paid positive Diophantine certificate of
**132=67M+65A**, with **49 positive existential coordinates and34
equations**. Its sum-of-squares polynomial costs **233=101M+132A** and
has exact total degree40. Both native kernels, their common exponent,
the bit mask, the output remainder and all required bounds are included.

This closes a specific input-recoding primitive relevant to PCP and
finite-alphabet word substrates. It is not yet a complete PCP universal
equation, and does not reduce the numerical75/88 bounds. It is also not
a witness-free polynomial loader: Section6 proves that no fixed
polynomial can compute (1) on every positive input.

## 1. Source, parameters and imported complete relations

The [source](native_binary_input_dilation132.py) exposes `build()` with
parameters x,z, a literal binary-operation DAG,49 positive auxiliaries
and34 comparisons. Its [receipt](native_binary_input_dilation132.json)
records the complete DAG and operation totals.

The two imported components are unchanged arithmetic sources:

* [Linked binary geometry47](group_linked_binary_geometry47.md), using
  its shared-B build:47 operations,13 equations,19 positive auxiliaries.
* [Prescribed-scale AND64](native_binary_masked_selection63.md):64
  operations,16 equations,22 positive auxiliaries.

We use a proved extension of the first component's stated domain below.
The second component has positive parameters `(S,Hhat,Mhat,Ahat)` and
exactly asserts

    S is dyadic, 0<=Hhat-1<S, 0<=Mhat-1<S,
    Ahat-1=(Hhat-1) AND (Mhat-1).                    (2)

Here AND means ordinary binary bitwise AND. Its padding forces all four
Boolean classes to occur, including when some unpadded class is absent.
No bit typing is imported as an additional free assumption.

Supply eight additional positive coordinates

    q,P,J,K,Ahat,quotient_hat,input_slack,output_slack.

Compute

    Q=q^4, B=8Q, S=qP, Hhat=xJ+1, Mhat=K+1, N=Q-1,

and impose the five additional comparisons

    (B-1)J+1=P,
    (2B-1)K+1=S,
    x+input_slack=q,
    Ahat+Q=N*quotient_hat+z+2,
    z+output_slack=Q.                               (3)

Feed `(q,B,J)` to geometry47 and `(S,Hhat,Mhat,Ahat)` to AND64.
Every supplied coordinate is positive. Computed Hhat,Mhat,S are positive
before invoking (2), so no conditional-positivity step is hidden.

## 2. Geometry extension and exact exponent synchronization

The same shared-B geometry47 source has exact positive projection

    J>B, J odd, q=2^popcount(J)                       (4)

whenever q,B are positive and **B>=8q^2**. Its original statement used
B=8q^2. The extension follows from an exact positive witness transport.

Set B0=8q^2. The shared geometry source's only consumer of B is the
comparison `B+index_beta=J`. Given a positive zero at B>=B0, replace its
parameter B by B0 and its bound witness by

    index_beta0=index_beta+B-B0>0.

Every one of its13 comparison residuals is identical after this change,
and all other coordinates are unchanged. The original complete theorem
at B0 therefore proves J odd and q=2^popcount(J); the unchanged supplied
bound still gives J>B. Conversely, under (4), the original theorem at
B0 applies since J>B>=B0. Keep its native witnesses and replace its bound
coordinate by `index_beta=J-B>0`. This restores all13 comparisons at B.
Thus (4) is the exact positive projection, with every native positivity
and rank obligation inherited from the complete original theorem.

These substitutions compare existential witness sets in the proof.
They are not extra runtime instructions in the47-operation component.
Equivalently, the original bootstrap only needs
`r=J>B>=8q^2`, hence r>=9 and r>q; no equality B=8q^2 is needed after
that bound is established.

Our computed `B=8q^4` satisfies B>=8q^2 for every positive integer q,
before any kernel equation is used. Thus (4) gives `q=2^n` for some
n>=1. In particular B is dyadic, with

    B=2^(4n+3).

Equation (2) types S=qP as a power of two. Since q is already a power of
two and P is a positive integer, P is itself a power of two, say2^ell.
The first equation in (3) implies

    2^(4n+3)-1 divides 2^ell-1.

For positive integers d,ell, `2^d-1` divides `2^ell-1` iff d divides ell:
reduce ell modulo d and use `0<2^r-1<2^d-1` when0<r<d. Consequently
P=B^h for an integer h>=1, and

    J=1+B+...+B^(h-1).

Its binary1 digits occupy distinct positions, so popcount(J)=h.
Combining this with q=2^n=2^popcount(J) forces **h=n**. Also J>B forces
n>=2. Thus all exponent sharing is proved:

    q=2^n, Q=2^(4n), B=2^(4n+3), P=B^n,
    J=sum_(j<n) B^j, n>=2.                          (5)

No supplied logarithm, word length or separate same-duration assumption
is used. The second equation of (3) then gives uniquely

    K=sum_(j<n) (2B)^j,
    S=qP=(2B)^n.                                    (6)

## 3. Mask extraction and folding

The input bound in (3) gives0<x<q. Write its binary digits as
`x=sum_(j<n) x_j 2^j`, including harmless high zero digits, and let
`d=4n+3=log2(B)`.

The integer `xJ` consists of n copies of the n-bit word x, at positions
d i for0<=i<n. Since d>n, these copies do not overlap and their sum has
no carries. The j-th1 of K is at position

    (d+1)j=dj+j.

It selects bit j from copy j. Equations (2), (5) and (6) therefore imply

    A:=Ahat-1=(xJ) AND K
      =sum_(j<n) x_j 2^((4n+4)j).                   (7)

Modulo `N=Q-1=2^(4n)-1`, exponent `(4n+4)j` is congruent to4j.
The folded value is

    Z=sum_(j<n) x_j 2^(4j),
    0<Z<=(Q-1)/15<Q-1.                             (8)

The upper bound is non-strict at x=q-1, which is allowed. The decisive
strict inequality is Z<Q-1.

The fourth equation in (3) is exactly

    A=N*(quotient_hat-1)+z.                          (9)

Thus z is congruent to Z modulo N. The final positive bound gives
`0<z<Q`, or1<=z<=N. There is exactly one such representative of the
nonzero residue Z, so z=Z=spread4(x). This proves soundness.

## 4. Full positive converse

Given arbitrary positive x and z=spread4(x), choose any n>=2 with
x<2^n. Define q,Q,B,P,J,K by (5)--(6) and A by (7). The right side of
(8) is independent of the high zero padding implicit in the choice of n.
Set

    Ahat=A+1,
    quotient_hat=(A-z)/(Q-1)+1,
    input_slack=q-x, output_slack=Q-z.

All are positive integers. In particular A>=z termwise, since each
exponent in (7) is at least its exponent in (8), and A-z is divisible by
Q-1. The shift in quotient_hat is necessary: x=1 gives A=z=1 and the
unshifted quotient is zero. All five comparisons (3) hold.

The geometry47 converse applies because J>B, J is odd and its population
is n. To apply the complete AND64 converse, its scale S=qP is dyadic,
and the two nonnegative inputs are strictly below S:

    xJ < qP=S, K=(S-1)/(2B-1)<S.

Thus the full positive AND witnesses exist for A=(xJ) AND K, including
any absent unpadded Boolean classes. The imported kernels independently
provide19 and22 positive coordinates. There is no other compatibility
condition between their auxiliaries. This supplies all49 positive
witnesses and proves the exact projection (1).

The proof uses the complete kernel converses. The checker does not claim
to materialize their astronomical auxiliary Pell solutions for the
genuine linked geometries.

## 5. Exact arithmetic ledger and degree

The wrapper has the following literal costs:

| Wrapper computation | M | A |
|---|---:|---:|
| q2=q*q, Q=q2*q2, B=8Q, S=qP |4|0|
| B-1, (B-1)J, plus1 |1|2|
| B+B, minus1, (2B-1)K, plus1 |1|3|
| xJ, Hhat=xJ+1, Mhat=K+1 |1|2|
| x+input_slack, Q-1 |0|2|
| N*quotient_hat and both sides of (9) in form (3) |1|3|
| z+output_slack |0|1|
| Total |8|13|

In particular doubling B is one addition. The two kernels contribute
47=26M+21A and64=33M+31A, giving132=67M+65A. There are34 comparisons
and49 positive witnesses, with x,z the two free positive parameters.
Squaring each residual and summing costs another34M+67A, giving the
233-operation polynomial stated above.

Every certificate residual has total degree at most20. This follows
also from the literal DAG's structural degree audit. The prescribed AND
scale is `16qP`, of degree2 in the independent supplied coordinates.
Its first norm residual has unique degree20 leading term

    and_w^2 * and_s^4 * and_k^2 * (16qP)^6.

All other residuals have lower degree. Its nonzero square cannot cancel
against other squared leading forms. The full polynomial therefore has
exact degree40. The source checks the upper degree bound structurally
and the nonzero leading form by exact weighted univariate arithmetic.

## 6. Word coding and the PCP boundary

For a binary word w let `enc2(w)=2^|w|+value2(w)`, including
enc2(empty)=1. The primitive has the exact sentinel-preserving meaning

    spread4(enc2(w))=enc2(h(w)),
    h(0)=0000, h(1)=0001.                           (10)

This is an injective constant-length code for the input bits. It can be
extended to any alphabet of size at most16 by assigning distinct
four-bit blocks to its other symbols. Ordinary string equality and
concatenation are preserved; no parsing or tile selection is thereby
certified for free.

Iterating the complete relation r times gives block width4^r and admits
any fixed finite alphabet once r is large enough. With intermediate
positive outputs shared as variables, a literal r-stage certificate has
132r operations,34r equations and50r-1 positive existential coordinates.
One sum-of-squares polynomial costs234r-1 and still has degree40. This
is an explicit paid option, not an assertion that these costs are
competitive with the existing complete group compiler.

[Nicolas, Sections2--3](https://arxiv.org/pdf/0802.0726) explicitly uses
injective binary word codes and delimiters in reducing semi-Thue
accessibility to generalized PCP. That reduction does not supply a free
affine ordinary-integer loader for the recoded input. The present theorem
pays one uniform coding primitive; a fixed-program PCP input convention,
its boundary words, selected tile histories and their acceptance relation
still require a complete composition proof. No universality is inferred
from undecidability of variable PCP instances.

There is also a simple obstruction to replacing this bridge by any
fixed arithmetic circuit with only addition, subtraction and
multiplication and no existential variables. Such a circuit computes a
polynomial f(x). If it computed spread4, then
`f(2^n)=16^n=(2^n)^4` for infinitely many n, so f(x)=x^4 identically.
But spread4(3)=17 differs from3^4=81. The required recoding is therefore
not a witness-free polynomial function, despite its quartic growth on
powers of two.

## 7. Finite verification and its limits

The checker compares all34 source residuals against separately assembled
kernel and wrapper formulas on512 positive and256 signed assignments,
and checks each full sum-of-squares value. It audits all gates, domains
and the exact degree40 leading term.

Genuine outer fixtures verify synchronized geometry, separated copies,
bitwise selection, folding, shifted quotients and positive padded Boolean
fields. They include every x<2^n for2<=n<=10 and512 larger random cases,
all-ones inputs and the zero unshifted quotient at x=1. Additional checks
cover512 changes of padding length,2,048 independent string codes and
their width16 iterations, and4,096 dyadic synchronization candidates.
These are complete outer arithmetic fixtures, not claimed full Pell
zeros. The infinite positive-kernel extension is the proof in Section4.

Run the source normally to compare its deterministic receipt, or with
`--write-receipt` to regenerate it.

Independent `native_controller` review passed the complete proof, source
and fresh default replay with no findings. The review additionally
verified512 positive raw-geometry witness transports, checking all13
residuals at B and B0, and512 independently generated radix16 extraction
and folding cases through120 input bits. It checked every positive
converse coordinate, the shared exponent, paid kernel interfaces and
the exact degree40 leading form. Root's independent proof/source review
and default replay also passed. These finite supplements do not claim
to construct the full astronomical Pell witnesses.
