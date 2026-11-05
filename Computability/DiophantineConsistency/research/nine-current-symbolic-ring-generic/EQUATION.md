# Symbolic nine-variable equation

Let the nine unknowns `u, v, h, s, w, φ, i, j, t` range over **all nonnegative integers**. The following is a readable transcription of `NineCurrentRing.eval_current`; the theorem gives the precise Lean-bound ring formula. The helper symbols below are definitions, not additional unknowns. No claim about the operation count or degree of an expanded graph is made here.

The fixed seed is the quartic gate syntax `seed = QuarticSyntax.expression left right`, where `left` and `right` are the two natural parts of `ObjectCurrentEquation2011.naturalExpression`, with their witness indices renamed into the right summand. Let `ν = QuarticCompiler.witnessCount left right`. Thus the seed and `ν` are determined by the current 2011 equation and its four fixed ports. Define the following closed coefficient recipes from `ExecutableJonesCore`:

* `L = 5^(ν+1)`; `Star` is the finite set of vectors `k : Fin (ν+2) → ℕ` whose entries sum to 4.
* `expo(k) = Σ_{r=0}^{ν} k(r+1) 5^r`.
* `p(k) = (∏_r k(r)!) · coefficient(expand(seed), (r ↦ k(r+1)))`, using `SyntaxCoefficients` for the signed integer coefficient.
* `z = 2^(2 + Σ_{k∈Star}|p(k)|)`.
* `y₀ = toNat(Σ_{k∈Star}(z+p(k))(2z)^(L−expo(k)))`, where `toNat` is Lean's nonnegative truncation of an integer. These are fixed numbers, not unknowns.

Set

\[
\begin{aligned}
b&=y_0+1+u,& B&=b^5,& q&=B^L,& N&=q^{16},\\
e&=\sum_{k\in\mathrm{Star}}(z+p(k))B^{L-\operatorname{expo}(k)},&
\ell&=\sum_{r=0}^{\nu-1}B^{5^{r+1}},&
\lambda&=\sum_{r=0}^{4L-1}B^r,\\
g&=v+1,& \theta&=B-2z,& G&=32bB^{5^\nu}.
\end{aligned}
\]

Using the `rankCode` definition from `JonesSyntaxCore`, put

\[
\begin{aligned}
R={}&\bigl(g+eq^3+\ell q^5+
 [2(e-z\lambda)(1+B+g)^4+\lambda B+\lambda Bq^4]q^7\bigr)(N^2-N)\\
&+\bigl(q^3-b\ell+\ell+\theta\lambda q^3+(B-2)q^8\bigr)(N^2-1).
\end{aligned}
\]

For the remaining named quantities, write `h₁=h+1`, `s₁=s+1`, `w₁=w+1`, `i₁=i+1`, `j₁=j+1`, and define

\[
\begin{aligned}
U&=N^2w_1,& Y&=N^2s_1,& M&=RY,& P&=2M^2U,\\
K&=R+1+h_1(P-1),& A&=M(U+1),& B'&=2R+1,& W&=bw_1,\\
C&=B'+W+\varphi,& J&=4A-5,& Q&=3WC-2(W^2-1),\\
D&=(A^2-1)C^2+1,& E&=i_1JDC^2,& F&=(A^2-1)E^2+1,\\
G'&=A+F(CD+1-A),& H&=B'+j_1C,& I&=(G'^2-1)H^2+1.
\end{aligned}
\]

Finally set

\[
\begin{aligned}
A_0&=(P^2-1)K^2+1,& A_1&=DFI,& V_0&=A_0^2+2,& V_1&=A_1^2+2,\\
B_d&=(JF)^2,& C_d&=(QF+J(H-C))^2,&
D_m&=K^2G-4(C-KY)^2G-8gK^2,\\
K_c&=B_d(2D_m-1),& T&=B_dt+C_d-K_c(C_d+V_0V_1).
\end{aligned}
\]

The equation is

\[
\boxed{(T^2+K_c^2A_0-K_c^2V_0^2A_1)^2-4T^2K_c^2A_0=0.}
\]

The checked client proves that this `Expr (Fin 9)` has no natural zero iff the mapped native ZFC-refutation formula is false, as a derivation in standard iPRA; it also checks the corresponding mapped Gödel–Gentzen consistency form. The Lean theorem establishes the binding of the named ring formula above to that syntax. The human transcription and the textual interpretation of the coefficient recipes require independent review; no claim is made that Lean read this Markdown or any gzip file.
