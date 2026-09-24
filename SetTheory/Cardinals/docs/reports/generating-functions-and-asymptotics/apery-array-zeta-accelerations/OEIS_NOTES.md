# Mathematical notes for the targeted OEIS formulas

> Notation: these notes use `U` for the cubic potential and `V` for the
> quadratic one. The article renames them `Phi` and `Psi`, reserving `U`
> for the A108625 array itself; see the notation paragraph in Section 1.2
> of the article. Nothing else differs.

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
is zeta(2). This proves the entry's superdiagonal and subdiagonal
families for every k >= 0, as the formula field states them. The signed
error at (m,n) has sign exactly (-1)^m.

Note on scope: the formula field of A108625 already states both families
for k = 0,1,2,... (Peter Bala, Jul 23 2008; internal revision 98,
May 30 2026). What is supplied here is a proof, not a wider statement.

## Shifted-diagonal recurrence for A143007

With k fixed, D_n = T(n,n+k), sigma_n = (2n+k)(3n^2+3nk+k^2),
w_n = n^3(n+k)^3, G_n = (2n+1)(n^2+n+2(n+k)^2+2(n+k)+1) and
K_n = sigma_{n+1}(sigma_n*G_n - n^6) - sigma_n*(n+1)^6,

    w_{n+1}*sigma_n*D_{n+1} = K_n*D_n - sigma_{n+1}*w_n*D_{n-1},
    D_0 = 1, D_1 = 2k^2+6k+5.

The companion Dhat_n = D_n * S^(3)_{n,k} satisfies the same recurrence,
with Dhat_0 = H_k^(3), Dhat_1 = D_1*H_k^(3) + sigma_1/(k+1)^3, and

    Dhat_n*D_{n-1} - Dhat_{n-1}*D_n = sigma_n / w_n.

At k = 0 this is the classical (n+1)^3*A_{n+1} =
(34n^3+51n^2+27n+5)*A_n - n^3*A_{n-1} together with 6/n^3.
D_n is always an integer; Dhat_n need not be.

No analogous all-k recurrence for A108625 is proved here; the zeta(2)
recurrence (n+1)^2*b_{n+1} = (11n^2+11n+3)*b_n + n^2*b_{n-1} is
established only on the main diagonal.

## Suggested citation posture

Preserve Peter Bala's attribution for the conjectural formulas. Describe
the article as an explicit finite-certificate proof. Do not state an
unverified priority claim for the broad acceleration method, which is
classical. Any note must also cite Ofir David, "The conservative matrix
field", arXiv:2303.09318v3 (Examples 16, 19, 25; Section 5), which
already contains closely related conservative fields and, up to duality
and sign conventions, the same conjugate polynomials. A public, stable
bibliographic location and normal OEIS review would be needed before a
formal reference could be added to the entries.
