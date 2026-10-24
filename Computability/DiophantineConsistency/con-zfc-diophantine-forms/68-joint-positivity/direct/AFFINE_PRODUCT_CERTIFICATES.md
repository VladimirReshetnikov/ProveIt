# Affine, pairwise-coprime weights instead of exponential formula codes

## Exact arithmetic lemma

Let m>=1, and let M be a positive integer divisible by every integer from1 throughm. For0<=j<=m set f(j)=1+jM. Then f(0)=1, every f(j)>1 forj>0, and distinct positive labels have coprime weights.

Proof: if i<j and d=gcd(1+iM,1+jM), then d divides(j-i)M. Also gcd(d,M)=1, because every common divisor divides1. Hence d dividesj-i. Since j-i<=m, it divides M by hypothesis; thus d divides M and d=1.

Consequently, equality of products of these weights is exactly equality of positive-label multisets. To see this even though the weights need not be prime, choose any prime divisor of f(j). It divides no other weight; its valuation in a product determines the multiplicity ofj.

## Closed finite certificate, but not fixed-dimensional polynomial

Use the uniform two-premise C222 rules from COMMUTATIVE_CERTIFICATES.md. Let N be a finite number of instances, each with labels p_i,q_i,c_i in[0,m]. Then

    product_{i<N}(1+c_i M)
      = (1+M) product_{i<N}(1+p_i M)(1+q_i M)

is equivalent to the commutative balance for target1, modulo the free truth coordinate0. Therefore existence of N,m,M and these finitely many valid rule instances is equivalent in ZFC to a ZFC refutation.

Unlike the radix encoding, the labels occur AFFINELY, not as variable exponents. Unlike prime coding, no primality test or nth-prime relation is needed. The arithmetic source is nonetheless NOT yet a single fixed ordinary polynomial: variable-length products, the rule list, its local validity, its bounds, and divisibility of M by the interval must still be compiled. Taking M=m! proves existence but does not make factorial a polynomial.

## One multiplicative accumulator

The product identity can also be witnessed by a path of positive integer accumulators S_0,...,S_N with

    S_0=1+M, S_N=1,
    S_{i+1}(1+c_i M)=S_i(1+p_i M)(1+q_i M).

Soundness: multiplying all equations and cancelling the positive internal S_i gives precisely the product identity. In fact positivity of the S_i need not be separately postulated if S_0=1+M and the displayed equations hold over naturals: all factors are positive, so S_i>0 inductively. No stack decoding or chronological proof semantics is needed.

Completeness: start with the sole open obligation1. Select an open proof-tree node labelledc_i and replace it by its two padded premises p_i,q_i. Let S_i be the product of f(j) over all open obligations. Removing the selected factor f(c_i) and inserting the two premise factors gives exactly the displayed update. Axiom nodes insert only0, whose factor is1. After all finite proof-tree nodes have been expanded, S_N=1.

The local accumulator update has total degree5 in S_i,p_i,q_i,M (degree3 if M is treated as a parameter). Its polynomial is

    S_{i+1}(1+c_i M)-S_i(1+p_i M)(1+q_i M).

It uses only multiplication, addition and subtraction. Combine its square with the local Horn-rule square and natural bound witnesses to obtain a local polynomial relation. This is a new arithmetic source architecture, not a completed small consistency polynomial. It avoids code-index exponentiation and formula primality at the source, while leaving a clearly isolated global compiler obligation.

## Why an arbitrary large M is not sufficient

M must provide pairwise coprimality (or another proved collision-free condition), not merely be large compared with the labels. The smallest counterexample M=1 gives f(1)=2, f(3)=4, so two occurrences of label1 and one occurrence of label3 have the same product. The condition M divisible by the differences eliminates all such collisions simultaneously.

## Comparison with the previous source

The one-stack source preserves an ordered list of pending formulas by quadratic Cantor pairing. The present accumulator represents an UNORDERED multiset by a product of coprime linear factors. Neither proof ranks nor a decoding function for an entire stack is needed. The logical flow theorem is what makes discarding order sound. All claims above are elementary mathematical theorems, not a claim that a compiler has already produced fewer final Diophantine variables or operations.

## Fully specified global constructor proposal

`AffineProductEquation.lean` is emitted from the exact local residual JSON by `emit_affine_constructor.py`. It is a closed constructor proposal against the same pinned APIs as round9, NOT a compiled theorem or a materialized polynomial.

The five outer natural parameters are t,x,y,m,M0, with M=M0+1. Define beta(x,y,i)=x mod(1+(i+1)y). Require:

1. beta(x,y,0)=M0+2 and beta(x,y,t)=1.
2. For every i<t, the local affine-accumulator relation holds between beta(i) and beta(i+1), with the SAME parameters m,M0. Every rule labelp,q,v has a natural slack showing it is at mostm.
3. For every j<m there is a natural k with M0+1=(j+1)k.

All local conditions are explicit ordinary polynomials. The two bounded universal blocks use the existing direct bounded-forall representation constructor, and the remaining existential block uses the direct quartic compiler, deliberately stopping before Jones. No unspecified universal index or MRDP coefficient is supplied.

Soundness is the coprimality, telescoping and Horn-flow argument above, composed with the pinned C222 calibration. Completeness chooses any finite proof tree, lets m bound every formula label used, chooses M=m! (and M0=M-1), then builds the accumulator path by expanding its open obligations. The finite Chinese remainder encoding supplies x,y for all its accumulator values. The divisibility block has the quotients M/(j+1). These choices establish exactly the constructor's input predicate.

The arithmetic common multipleM, the beta sequence scale y, and the bounded-forall compiler's own CRT/majorization scales are DIFFERENT witnesses. Choose them in that order. No condition of the form M>=a bound depending quadratically on M is imposed. Setting any compiler scale equal toM would invalidate this argument and is not done by the constructor.

The provisional local quartic is `affine_step_quartic.json`:97 natural witnesses,92 quadratic residuals and3,026 monomials. Four exposed parameters S,Sp,m,M0 are not included in the witness count. This intentionally straightforward baseline can be replaced by branch-shared rule verification without changing the global theorem. The global compiler's witness count remains unmeasured; this component does not claim a smaller finished consistency equation.
