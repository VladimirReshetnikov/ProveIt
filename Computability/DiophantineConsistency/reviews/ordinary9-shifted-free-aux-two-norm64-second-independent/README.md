# Second independent review: nine-variable two-norm candidate

The pinned [candidate](../../research/ordinary9-shifted-free-aux-two-norm64/README.md)
has nine natural inputs, 64 live binary operations, and exact degree 60 for
fixed nonzero beta. Its standard-integer zero existence is equivalent to that
of the separate shifted-zeta **free-y² child** under nonnegative ports. The
original shifted parent still requires a square auxiliary witness; its reverse
bridge and any iPRA/consistency endpoint remain open.

The independent checker compares the complete ordered first/main expression
trees with the pinned 84-row child, verifies every reference and operation in
the nine-variable graph, and traverses backward from its output. All 64 rows
and all nine inputs are live. Its output is literally \(A_0^2+A_1^2\), so
a standard integer zero is exactly a simultaneous first/main norm zero.

For a child zero the four integer factors are units; independent exhaustive
mod-4 checks show its first and main factors cannot be −1, so both residuals
vanish and the same nine coordinates give a candidate zero. Conversely, a
candidate zero has nonnegative q, shifted \(s\ge1\), shifted
\(k=\eta+n_\zeta+1\ge1\), hence \(Y>0\) and
\(c=\eta+Yk>0\). The separately [reviewed completion](../ordinary13-free-aux-square-general-completion-second-independent/README.md)
then chooses the four dropped child inputs so its strong and auxiliary factors
are one, with arbitrary actual signed R and without changing either norm.
That argument completes the *relaxed* child; it does not provide a square
auxiliary witness for the original parent or prove the two-norm equation has
any zero.

For degree, put \(B=X+ac\), \(D_*=UB+HS\), and
\(\Delta=a^2+H\). Direct polynomial expansion, checked independently,
cancels the naively highest term:

\[
A_1=U^2(X^2+2Xac-1-Hc^2)+2UBHS+H^2S^2.
\]

With fixed ports and the nine witness inputs of degree one, the graph gives
\(\deg(U,X,a,c,H,S)\le(6,2,6,5,6,7)\). The three terms have degree
at most 28, 30 and 26. The separate first residual has degree at most 24;
therefore the sum of squares has degree at most 60. The main degree-30 term
comes solely from the middle term and is

\[
8\beta^{21}J^{21}w^2s_{\rm input}^5
(\eta+\zeta_{\rm input})\gamma_{\rm input}.
\]

Its square is a nonzero degree-60 term when beta is nonzero, while
\(A_0^2\) has degree at most 48. Independently evaluating the exact graph
as a sparse polynomial on the specified ray gives coefficient
\(64\beta^{42}\) at \(t^{60}\). The degree assertion treats the four
ports as fixed coefficients; it does not assert degree 60 at beta=0.

The checker additionally exhausts the generic first/main mod-4 unit cases and
verifies the cancellation identity as a free integer polynomial. The author
receipt and first independent review also reproduce. No Lean, build, staging,
model-provider validation, or proof-object existence check was performed.

```sh
python3 -I -S -B reviews/ordinary9-shifted-free-aux-two-norm64-second-independent/check.py | cmp - reviews/ordinary9-shifted-free-aux-two-norm64-second-independent/receipt.json
```
