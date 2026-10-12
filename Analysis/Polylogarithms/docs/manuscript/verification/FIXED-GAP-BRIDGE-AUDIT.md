# Independent algebraic audit of the fixed-gap determinant bridge

The incoming ordered-boundary, gap-six and gap-eight reports use a different
reduction of the same original moment matrix as Section 8.45. The following
derivation verifies its normalization for every half-gap, without inferring
the identity from the finite spot checks. It does not yet accept the Gamma
integral null basis or its large-index estimates.

Let (m=b-age1), (b>m), and set

\[
 A_r=\begin{cases}0&r\le m,\\(2r)^{\underline{2m}}&r>m,\end{cases}
 \quad B_N=(2N-1)^{\underline{2m}},\quad d_N=2(A_N+B_N),\quad
 \beta_j=2|B_{2j}|/(2j)!.
\]

The (B_{2j}) in the last expression are Bernoulli numbers. Define a lower
triangular matrix (T) of size (b+m): its first (m) rows are identity
rows; below them, (T_{NN}=d_N) and

\[
 T_{Nr}=-\beta_{N-r}(A_r+B_N),\qquad r<N.
\]

All (d_N) in these rows are positive. The first (m) columns of (T^{-1})
are exactly the fundamental recurrence solutions (R_{N,j}) initialized
by (R_{N,j}=\delta_{Nj}) for (N\le m). Their boundary block is

\[
 F_{b,m}=(R_{b+i,j})_{1\le i,j\le m}.
\]

Reverse the original matrix's columns by writing (r=b-k), and put

\[
 N=m+t+1,\qquad j=N-r=t+k-a+1.
\]

Direct factorial cancellation in the original matrix gives, for (j\ge0),

\[
 M_{t,k}=\frac{(2t+1)!}{(2r)!}\mu_j(A_r+B_N),
 \qquad \mu_j=B_{2j}/(2j)!.
\]

The convention excluding lower binomial index zero is precisely the
condition (A_m=0). The entry is zero for (j<0). For (j>0),

\[
 \mu_j=(-1)^{j-1}\beta_j/2,
\]

and for (j=0), (\mu_0=1) and (T_{NN}=2(A_N+B_N)). Thus all entries,
including the diagonal, have the same exact description

\[
 M_{t,k}=\frac{(2t+1)!}{(2r)!}\frac{(-1)^{N-r}}2\,T_{N,r}.
\]

The selected rows are (m+1,\ldots,m+b), and the selected columns are

\(1,\ldots,b\), in reverse order. Removing the row/column signs and the
factorials contributes

\[
 \frac{(-1)^{bm+b(b-1)/2}}{4^b b!},
 \qquad
 \frac{\prod_{t=0}^{b-1}(2t+1)!}{\prod_{r=1}^b(2r)!}
 =\frac1{2^b b!}.
\]

Jacobi's complementary-minor identity for (T) gives

\[
 \det T_{\{m+1,\ldots,m+b\},\{1,\ldots,b\}}
 =(-1)^{bm}\det T\det F_{b,m},\qquad
 \det T=\prod_{N=m+1}^{b+m}d_N.
\]

The two factors ((-1)^{bm}) cancel. Consequently, at every admissible
pair, the identity used by those reports is

\[
 \boxed{\det M_{b-m,b}=
 \frac{(-1)^{b(b-1)/2}}{4^b b!}
 \left(\prod_{N=m+1}^{b+m}d_N\right)\det F_{b,m}.}
\]

Every multiplier is explicitly nonzero. This proves equivalence of the two
rational nonvanishing predicates. The independent written argument settles
the sign and all row/column factors; finite computational comparisons have
a separate diagnostic role. The analytic claims needed for complete fixed
gap-six/eight families remain separate proof-audit work.
