# Independent review of the compact norm and midpoint shift

This is an internal mathematical and computational review, not external peer review or an end-to-end proof-assistant certificate. It applies to the literal files hashed in `COMPACT_INDEPENDENT_AUDIT.json`.

## 1. Universal four-root identity

Let `a,b,c,d,x` be independent indeterminates. Set

    p=ab, q=cd, u=a+b, v=c+d, s=x^2-u-v,
    K=s^2-4uv+4(p+q),
    L=-4(s+2v), M=-4(s+2u), N=-8.

The norm over all sixteen independent signs of the first four square roots is

    N4(x;a,b,c,d)
      = [K^2+pL^2-q(M^2+pN^2)]^2
        -p[2KL-2qMN]^2.

To prove this identity, work first in the formal biquadratic algebra with `r^2=p` and `t^2=q`. The two squared pair roots are `u+2r` and `v+2t`. Their two-root norm expands as

    (x^2-u-v-2r-2t)^2-4(u+2r)(v+2t)
      = K+Lr+Mt+Nrt.

Take its norm with respect to `t`. The result is

    [K^2+pL^2-q(M^2+pN^2)] + [2KL-2qMN]r.

Taking the norm with respect to `r` gives the displayed expression. The four choices of the two pair signs, together with each pair's overall sign, are exactly the sixteen independent signs of the original four radicals. This is an identity in an integer polynomial ring; no independence or positivity assumption on specialized radicands is needed.

## 2. Universal five-root identity and the compact DAG

Adjoin `w` with `w^2=e`. Evaluate the four-root expression at `x+w`, obtaining `A+Bw` by ordinary polynomial arithmetic. Its norm is

    A^2-eB^2=N4(x+w;a,b,c,d)N4(x-w;a,b,c,d).

This is precisely the product of all thirty-two conjugate linear factors, hence the five-root norm. The quadratic-algebra rules used by the compact evaluator are

    (A+Bw)(C+Dw)=(AC+eBD)+(AD+BC)w,
    (A+Bw)^2=(A^2+eB^2)+2ABw,
    Norm(A+Bw)=A^2-eB^2.

They involve only integer additions, subtractions and multiplications. The literal generic DAG has 99 live binary operations: 27 additions, 10 subtractions, 62 multiplications.

`independent_compact_audit.py` constructs the norm independently by successive sign conjugation in a formal multiquadratic algebra. It does not import or execute a builder. The four-root identity agrees in all 495 coefficients. The five-root generic DAG agrees in all 20,349 coefficients. These are exact integer symbolic identities, not evaluations at finitely many points. The audit receipt records hashes of their full coefficient lists.

## 3. Exact midpoint shift

In the thirteen-variable construction put

    L=8H(2Q-1)V,
    C4=256H^2(Q-1)(QV^2-1),
    K=64H^2 V^2+256H^2(Q-1).

Then the exact polynomial identity

    L^2-C4=K

follows from `(2Q-1)^2-4Q(Q-1)=1`. It is also checked coefficient for coefficient by the independent audit.

The shifted carrier is `Z+L`, where `Z=H(2t+1)+b0`. This is the unshifted carrier under the integral coordinate bijection

    t_unshifted=t+4(2Q-1)V.

Neither `Q` nor `V` depends on `t`, so the inverse is obtained by subtraction. Solvability is preserved exactly.

Pair the two conjugate factors belonging to the last radical. For any signed sum `S` of the first four roots, their product is

    (Z+L-S)^2-C4=(Z-S)^2+2L(Z-S)+K.

There are sixteen such factors. In the actual packet the ordinary degrees of the first four radicands are `46,14,56,30`, so their radical weights are `23,7,28,15`. Also `deg Z=7`, `deg L=59`, `deg K=58`. Consequently each paired factor has weighted degree at most `87`, and their product has ordinary polynomial degree at most `16*87=1392`.

The unique top-weight term in each factor comes from the third radicand's root in `-2LS`. Thus the degree-1392 leading homogeneous part is

    2^16 * leading(L)^16 * leading(C2)^8.

On the recorded actual-coefficient line modulo `1000000007`, this has nonzero coefficient `756708762`; a separate dense univariate evaluation of the literal DAG gives the same coefficient at degree 1392 and no higher term. This supplies both an algebraic upper bound and an attained lower bound. The naive degree propagation through the unsimplified DAG gives 1888 and is not itself the degree proof for this variant.

## 4. Literal audit results

Every advertised input and binary operation is live. References are topologically ordered, and only integer constants, declared input ports, addition, subtraction and multiplication occur in the compact DAGs. The six fixed coefficient payloads pass their gzip/raw SHA-256 bindings, lengths, bit counts and explicit elementary-constant identities. Each compact DAG also passes 128 modular comparisons against its independently parsed source packet at two primes. These modular comparisons supplement the exact norm and degree identities; they are not presented as a proof of an arbitrary polynomial identity.

The principal verified variants are:

| Variables over the integers | Exact degree | Live binary operations |
|---:|---:|---:|
| 13, direct carrier | 1888 | 205 |
| 13, shifted carrier | 1392 | 211 |
| 14, unit-product finalizer | 862 | 150 |
| 15, unit-product finalizer | 204 | 128 |
| 16, centered sum of squares | 120 | 123 |

All listed counts are relative to the explicit convention: every live binary addition, subtraction and multiplication costs one; fixed integer leaves and reuse are free. The large fixed coefficients remain part of the equation and are not treated as quantified variables.
