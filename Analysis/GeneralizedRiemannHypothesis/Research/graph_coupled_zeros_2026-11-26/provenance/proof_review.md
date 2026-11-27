# Independent mathematical review of the graph theorem

## Hypotheses

For the finite theorem, each F_i is monic of positive degree d_i, and every
input root is real; repetitions and coincidences across vertices are
allowed. The graph is undirected, connected, and has positive edge weights.
Set n to the number of vertices and N=sum d_i. The one-vertex convention is
tau=1 and L^+=0. For N=1 the output is constant and its root list is empty.

V is the N-by-n incidence matrix assigning each listed root to its vertex.
Thus V 1_n=1_N. Lambda is the diagonal matrix of the listed roots and
Q=I_N-1_N 1_N^T/N. Define

    K = Q Lambda Q - Q V L^+ V^T Q.

K is symmetric, annihilates 1_N, and its relevant restriction acts on
1_N-perp. No orthonormal basis needs to be numerically constructed.

## Exact determinant identity

For z avoiding the original roots, let M=zI_N-Lambda. Then

    P_L(z) = det [[ M, V ], [ -V^T, L ]].

This follows by taking the Schur complement of M. Choose an orthonormal
basis on the vertex side whose last vector is e=1_n/sqrt(n). Eliminate
the restriction of L to e-perp. Its determinant is n*tau, and the remaining
bordered matrix has upper-left block M+V L^+ V^T and border V e=
sqrt(N/n) 1_N/sqrt(N). Expansion of this last border gives

    P_L(z) = N*tau*det_{1_N-perp}(zI-K).

The identity extends to all z because both sides are polynomials. In
particular P_L has exact degree N-1, leading coefficient N*tau, and only
real roots. It is not merely an argument away from the poles.

## Edge update and centroid

For b=e_i-e_j and h>0, replacing L by L+h b b^T gives, on 1_n-perp,

    L_new^+ = L^+ - h/(1+hR) L^+ b b^T L^+,
    R = b^T L^+ b.

Consequently K_new-K=h/(1+hR) q q^T, with q=Q V L^+ b. Since every
d_i is positive, q cannot vanish: Vx constant on the N root coordinates
forces x constant on the vertices; x=L^+b also has sum zero. This would
imply b=0. Thus the update has rank exactly one. Standard Hermitian
interlacing and monotonicity apply even when roots are repeated.

The exact sum-of-roots identity is

    sum(output roots)
      = (N-1)/N * sum(input roots)
        - (1/N) sum_{i<j} d_i d_j R_ij.

The sum on the right is over **unordered** pairs. An ordered sum would
require 1/(2N). This follows from tr K and V^T Q V=diag(d)-d d^T/N.

The centroid and finite-N compression formulas do not automatically
extend to infinite zero lists: such sums diverge without a specified
regularization.

## Exact shared-root multiplicity

This argument applies to an arbitrary Hermitian matrix A, provided the
input real entire functions have strictly decreasing logarithmic
derivatives between their real zeros. In particular it applies to the
positive-degree real-rooted polynomials above and to the completed
arithmetic functions under the supplied critical-line input.

At a real a let S={i:F_i(a)=0}, T its complement, and m_i be the zero
order for i in S. Put

    C_0 = A[T,T] + diag_{i in T}(F_i'(a)/F_i(a)).

Then

    ord_a P_A = sum_{i in S}(m_i-1) + dim ker C_0.

Proof: with w=z-a, the S-block is diag(m_i)/w+B(w), so its inverse is
w diag(1/m_i)+O(w^2). Its Schur complement on T is E(w), with

    E(0)=C_0,
    E'(0)=diag_{i in T}(F_i'/F_i)'(a)
             - A[T,S] diag(1/m_i) A[S,T].

The derivative is negative definite. On ker C_0 this makes the first
nonzero determinant term exactly of degree dim ker C_0. The S-block
contributes a pole of order |S|, and the product of inputs a zero of order
sum m_i. This proves the formula, including S or T empty.

Useful consequences: a shared simple root of every input disappears;
a root away from every input has multiplicity exactly dim ker(A+D(a));
the coupling can create additional multiplicity at a partially shared
root through the complementary nullity. Multiplicities cannot be assessed
by simply subtracting one from every vanishing input and stopping there.

## Entire-function and interlacing check

For a real entire function of order at most one with only real zeros,
the canonical product gives

    Im(F'/F)(z) = -Im(z) sum_r m_r/|z-r|^2

away from its zeros. If every input has at least one zero, the imaginary
part of A+diag(F_i'/F_i) is definite for nonreal z. This proves its
invertibility. Multiplication by the inputs clears the apparent poles,
so P_A is a nonzero real entire function with only real zeros.

For A_t=A_0+t v v^*,

    P_{t+h}/P_t = 1+h v^*(A_t+D(z))^{-1}v.

The scalar function on the right is Herglotz for h>0. Its uncancelled
zeros and poles are simple and interlace. Common factors must be removed
before stating strict interlacing. At a simple ordinary zero with kernel
vector u, implicit differentiation gives

    da/dt = |v^*u|^2 / sum_i[-(F_i'/F_i)'(a)]|u_i|^2 >= 0.

The arithmetic functions have infinitely many zeros, so the required
strictness is available. Zero-free exponential inputs need separate
treatment; stating this theorem for all LP inputs without a nonzero
condition can accidentally include an identically zero determinant.

## Exact checked examples

`verify_graph.py` uses rational SymPy arithmetic. It checks six base
models: the degree-one constant-output boundary, a one-vertex derivative,
two linear factors, a three-vertex path,
a triangle, and a four-cycle. The checks cover the complete compression
identity, exact degree, leading coefficient, resistance centroid, and
every original-root collision in those cases. Four edge changes include
an increase of an existing edge, addition of an absent edge, and a
transition through a shared-root collision. All checks passed.

In the collision example,

    F_1=z^2, F_2=z(z-2), F_3=(z-1)(z-3),
    w_12=1, w_23=4/3,
    P_L=(4/3) z^2 (6z^3-16z^2-7z+26).

At z=0 the baseline sum(m_i-1)=1 and the complementary nullity is one,
giving multiplicity two. Increasing w_23 to 5/3 reduces that multiplicity
to one and increases the sum of all output roots by exactly 1/5.

These are finite exact checks supporting the proofs. They are not a
Lean proof, a verification of all possible graphs, or a new replay of
the upstream GRH development.

