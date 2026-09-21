# Mathematical notes for the targeted OEIS formulas

These are preparation notes only. No OEIS changes or submissions have been made.
The full proof, definitions, signs, and boundary cases are in `article.pdf`.

## A143007

Use square-array coordinates:

T(m,n) = sum_j binomial(m,j) binomial(m+j,j)
                  binomial(n,j) binomial(n+j,j).

For a=T(m-1,n-1), b=T(m,n-1), c=T(m-1,n), d=T(m,n), and
s=(m+n)(m^2+mn+n^2), the finite identities are

    m^3*d + n^3*a = s*c,
    n^3*d + m^3*a = s*b.

They imply closure of the horizontal and vertical edge weights

    h(m,n) = 1/(m^3*T(m-1,n)*T(m,n)),
    v(m,n) = 1/(n^3*T(m,n-1)*T(m,n)).

Their potential U satisfies

    U(m,n)-U(m-1,n-1) =
      (m+n)(m^2+mn+n^2)/(m^3*n^3*T(m-1,n-1)*T(m,n)).

The boundary values are U(0,k)=H_k^(3), and U(m,n) tends to zeta(3)
as max(m,n) tends to infinity. Summing along (n,n+k) proves the exact
conjectural family for every integer k >= 0.

## A108625

Use C(m,n) = sum_j binomial(m,j) binomial(m+j,j) binomial(n,j),
with dimension parameter m and radius n. It is not symmetric.

For a=C(m-1,n-1), b=C(m,n-1), c=C(m-1,n), d=C(m,n), and
q=n^2+(m+n)^2, the identities are

    2*n^2*d - m^2*a = q*b,
    m^2*d + 2*n^2*a = q*c.

They imply closure of

    h(m,n) = 2*(-1)^(m+1)/(m^2*C(m-1,n)*C(m,n)),
    v(m,n) = (-1)^m/(n^2*C(m,n-1)*C(m,n)).

The resulting potential V satisfies

    V(m,n)-V(m-1,n-1) =
      (-1)^(m+1)*(n^2+(m+n)^2)/(m^2*n^2*C(m-1,n-1)*C(m,n)).

Its boundary values are V(0,k)=H_k^(2) and
V(k,0)=2*sum_{j=1}^k (-1)^(j+1)/j^2. Its limit along escaping paths
is zeta(2). This proves both neighboring-diagonal conjectures and gives
all upper and lower shifted diagonals. The signed error at (m,n) has
sign exactly (-1)^m.

## Suggested citation posture

Preserve Peter Bala's attribution for the conjectural formulas. Describe
the article as an explicit finite-certificate proof. Do not state an
unverified priority claim for the broad acceleration method, which is
classical. A public, stable bibliographic location and normal OEIS review
would be needed before a formal reference could be added to the entries.
