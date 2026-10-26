# Thirteen positive unknowns, 76 operations, degree 96

This packet evaluates exactly the same polynomial as the accepted
[grouped-square77 equation](../thirteen-grouped-squares96/PROOF.md), with one
fewer paid operation. Every coordinate and every complete current2011 integer
port is unchanged. The maintained equation.tex/PDF is not changed.

The frozen parent graph is `../thirteen-grouped-squares96/polynomial.json`,
SHA-256 `05710557a8029ebdb378a6ac156f25e79b848eb10e673c01008acb415fc3e39d`.
Its ordinary proof is SHA-256
`6f2a4e7376dc05772fd98f7753f61ca9bf9c5081eb218a769da12d85ae7bf895`,
and its Lean source `ThirteenGroupedSquares96.lean` is SHA-256
`1b9aca9cb96c390ab074001c36680567969c6a33b6e556798b8394500d3cd424`.

## Full formula and exact identity

The thirteen strictly positive integer coordinates, in order, are
`J,F,alpha,f,i,T,s,w,n,eta,zeta,m,gamma`. The four fixed ports are
`beta,K0,MC,MF`; `MF` is the source mask shifted by beta exactly once.
All parent quantities are retained:

\[
\begin{gathered}
 b=\beta J,\quad q=b+1,\quad X=wq,\quad Y=sq^3,\quad E=XY,\\
 k=\eta+\zeta,\quad \ell=EkY,\quad c=kY+\eta,\quad a=E+Y,\\
 H=4a+3,\quad \Delta=a^2+H,\quad D=X+ac+\gamma H,\\
 C=q-F-\alpha,\quad
 R=(b(q-F)+\alpha)(q^2-1)+(M_C+qM_F)J,\\
 \tau=En+k-R,\quad P=\tau^2-\ell(\ell+k),\quad Q=D^2-\Delta c^2,\\
 G=(K_0+w)C-F,\quad L=cT-R,\quad V=f^2L-c,\\
 y=1+4\bigl(b(m-LVG)-G\bigr),\quad h=f^2-1,\\
 U=\Delta h(V^2-y^2)+y^2,\quad z=h-\Delta(bic^2)^2.
\end{gathered}
\]

The new literal graph evaluates

\[
 \boxed{p_{76}=(PQ-1)^2+(U-1)^2+z^2.}
\]

Writing the parent's strong norm as `Z=f^2-Delta*(bic^2)^2`, the two identities

\[
 \Delta f^2-\Delta=\Delta(f^2-1),\qquad
 (f^2-1)-\Delta(bic^2)^2=(f^2-\Delta(bic^2)^2)-1
\]

hold in every commutative ring. Hence `z=Z-1` and `p76=p77` identically.
No positivity, Pell norm, canonical-witness, or nonzero-factor premise is
needed for this identity. It preserves all assignments and therefore the
entire strictly positive zero set in both directions, by the identity map.
In particular the accepted entire-positive-zero equivalence with the
normalized72-operation product equation transfers without another sign
argument. The actual current2011 external Lean consistency endpoint also
transfers along equality of the two multivariate polynomials.

## Literal three-row replacement

The parent contains these four paid rows (not necessarily consecutive):

```text
scaled_f2    = Delta * f2
Theta        = scaled_f2 - Delta
normalized_Ns = f2 - strong_term
resZ         = normalized_Ns - 1
```

Replace them with these three rows:

```text
f2minus1 = f2 - 1
Theta    = Delta * f2minus1
resZ     = f2minus1 - strong_term
```

The first two occupy the old `scaled_f2` and `Theta` slots. The third occupies
the old `normalized_Ns` slot, before the later squares. The old later `resZ`
row is deleted. The other 73 parent rows are byte-for-byte identical in the
same relative order. This preserves topological evaluation and leaves every
gate, coordinate, and port live. The complete new graph has 76 paid binary
operations: 42 multiplications, 18 additions, and 16 subtractions. All squares
are paid multiplications; integer literals are leaves. No hidden rational
constant, extra variable, or exponentiation gate is introduced.

## Exact degree and whole constants

Since the polynomial is identical, its exact degree remains 96. The finite
auditor independently propagates every gate's full leading homogeneous
form. It resolves the entire 323-term main-norm cancellation, rather than
assuming that a preliminary degree upper bound is attained. With
`q0=beta*J`, `k0=eta+zeta`, and `C0=q0-F-alpha`, the degree-96 leader is

\[
 256q_0^{44}k_0^8s^{12}w^8f^{12}T^8C_0^4.
\]

It has 135 terms; the coefficient of
`J^48*eta^8*s^12*w^8*f^12*T^8` is exactly `256*beta^48>0` for the actual ports.
The three residual squares have degrees 80, 96, and 72. The auditor compares
every unchanged gate's leader with the pinned parent receipt, and compares
the full resulting leader, cancellation data, and whole coefficients.

The complete four current2011 integers remain 47,313 raw bytes and 4,230 gzip
bytes. They are reconstructed independently from the pinned full 3297-entry
native coefficient array and exact formulas for beta, K, MC, and MF_source.
Every decompressed integer, length, hash, and compressed copy is checked.
The exact formal output identity is checked with independent cut variables
at shared gates; comparison of all other rows binds that identity to the
entire actual graph. Corrupting the shared subtraction, its coefficient
use, the strong residual, or the tested square must change the formal output.
Schema, liveness, degree, and port corruption controls are checked separately.

## Validation boundary

`ThirteenSharedSquares96.lean` proves the uniform ring identity, actual
multivariate-polynomial equality, identity witness maps, and the actual
external `DiophantineConsistency.ConZFC` no-positive-zero equivalence. It
imports only the accepted grouped-square module. This is not an internal HA,
PA, or ZFC proof, and does not complete the remaining internal C222/runtime
calibration. It asserts no consistency or global minimality result.

The finite operation and degree calculation is separate from the Lean
polynomial identity. Its standalone standard-library auditor executes no
project or incoming program. Default and optimized Python runs compare
complete deterministic output bytes; only `--write` materializes this new
packet. The two new Lean leaves reuse the authenticated root grouped-square
cache, with exact source/object pins recorded in their author receipt; this
is not a fresh transitive source-closure validation.
