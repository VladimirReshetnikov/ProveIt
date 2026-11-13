# Directed-log exclusion of one compact partial family

The symbolic first-norm family in the [pinned partial construction](../ordinary9-shifted-two-norm-compact-first-compatible-partial/README.md)
cannot satisfy its actual main norm for **any** of its allowed eta or gamma
coordinates. A rigorous outward-rounded MPFR computation finds that a
conservative interval containing every possible main Pell index contains no
integer. This rules out that specific family; it does **not** rule out other
zeros of the nine-variable graph, provide a reverse bridge to its parent, or
prove a Lean/iPRA or consistency theorem.

The family uses the exact compact ports and fixes \(J=s=F=1\),
\(\alpha=2\), and \(w=(\beta-1)/2-K'>0\). Its first-Pell index is
\(n=(R+1)/2\), using the actual graph rank; the first norm is satisfied for
every natural \(0\le\eta<k\). Put

\[
X=qw,\quad Y=q^3,\quad M=XY^2,\quad
A=Y(X+1)+2,\quad A_f=2M+1.
\]

The fixed source recipes give \(q=2^{590069}\). The checker reconstructs
K′ and the two masks from the pinned definitions and ordered data, then
constructs these exact integers. It verifies \(n<A_f\) and \(2n<A\)
by exact integer comparison. If the main norm were zero, standard Pell descent
would yield a positive index m with \(c=Yk+\eta=y_m(A)\). The
[index-constraints packet](../ordinary9-compact-partial-main-index-constraints/README.md)
proves \(m<2n\) from the actual interval for c. The proof below does not
assume \(m=R\) or any sign of the actual signed main root.

## A conservative real-number envelope

Let \(\lambda_T=T+\sqrt{T^2-1}\). For the first norm,
\(k=2y_n(A_f)\), and for the main norm, \(c=y_m(A)\). The closed
Pell formulas imply

\[
m\log\lambda_A=n\log\lambda_{A_f}+K+\epsilon,
\quad K=\log\!\left(\frac{2Y\sqrt{A^2-1}}{\sqrt{A_f^2-1}}\right),
\]

where

\[
\epsilon=\log\!\left(\frac c{Yk}\right)
 +\log(1-\lambda_{A_f}^{-2n})
 -\log(1-\lambda_A^{-2m}).
\]

Here \(0\le\eta<k\), \(Y\ge8\), and \(A,A_f\ge2\). Thus
\(-1<\epsilon<2\): the first log is between 0 and 1, the second is
between −1 and 0, and the last contributes between 0 and 1.
Also \(0<K<2\). Indeed, using \(T-1<\sqrt{T^2-1}<T\),

\[
1<\frac{2Y(A-1)}{A_f}
 <\frac{2Y\sqrt{A^2-1}}{\sqrt{A_f^2-1}}
 <\frac{2YA}{A_f-1}
 =1+\frac1X+\frac2{XY}\le4,
\]

where \(X\ge1\) and \(Y\ge8\). For every integer T≥2,
\(0<\log(2T)-\log\lambda_T<1/T\): use
\(2T-1<\lambda_T<2T\) and the elementary logarithm bound
\(-\log(1-z)\le z/(1-z)\). The exact comparisons \(n<A_f\) and
\(m<2n<A\) therefore give the **strict** envelope

\[
\frac{n\log(2A_f)-2}{\log(2A)}<m<
\frac{n\log(2A_f)+5}{\log(2A)}. \tag{*}
\]

This envelope is deliberately much wider than the permitted eta interval.
It suffices to rule out the family if even its closed outward approximation
contains no integer.

## Reproducible directed calculation

The checker hashes its fixed sources; reproduces the bounded exact kernel
reconstruction; independently reconstructs the low and high masks; computes
R, n, A, and Af as exact binary integers; and evaluates (*) using MPFR
4.1.0. The lower input conversions, logarithm, multiplication, subtraction,
and final division are all rounded **toward negative infinity** (MPFR RNDD).
The upper side uses RNDU throughout. Division uses the upper denominator for
the lower bound and the lower denominator for the upper bound, after checking
positivity. The exact n is represented without rounding. Precision is
\(\operatorname{bitlength}(n)+192=2{,}360{,}467\) bits; explicit checks
bound the final quotient so that its floor and ceiling are exactly
representable at that precision.

The receipt records that `ceil(lower) > floor(upper)`, with a conservative
gap from the upper bound to the next integer greater than \(2^{-20}\).
Thus the enclosing **closed** interval has no integer, and the strict
interval (*) cannot contain the required Pell index. This conclusion depends
on the mathematical inequalities above, the pinned compact source recipes,
and correct directed-rounding semantics of the stated MPFR library. It is a
reproducible numerical certificate, not a kernel-checked Lean proof.

A preliminary guard test took about 0.5 s for a 524,288-bit logarithm and
about 3.9 s for a 2,400,000-bit logarithm in this environment. The checker
sets a 768 MiB process address-space cap, a 45 s CPU cap, and zero core-file
limit. The command below adds a 50 s wall-clock guard. Exact input integers
occupy at most about 590 kB each; transient MPFR allocations are covered by
the hard cap. No gigantic Pell coordinate is built, and no large numeral is
printed or written to disk. If a guard is exceeded or any assertion fails,
no exclusion should be inferred.

```sh
timeout 50s python3 -I -S -B research/ordinary9-compact-partial-directed-log-bound/check.py | cmp - research/ordinary9-compact-partial-directed-log-bound/receipt.json
```
