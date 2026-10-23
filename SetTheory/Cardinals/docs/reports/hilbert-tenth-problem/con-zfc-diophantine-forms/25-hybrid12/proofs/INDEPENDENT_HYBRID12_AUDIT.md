# Independent audit of Hybrid12

Reviewed source: `research/root_mergers/HYBRID12_PROOF.md` and the nine
JSON circuits emitted by `build_hybrid12.py`. Repository comparison pin:
`ae3007ca4467011e0e051c84acb4a1dd13971b0e`.

## Verdict and scope

The unweighted-carrier, square-weight construction has a valid ordinary
mathematical reduction to the inherited positive/signed-quotient normalized
blank-compiler interface. Its genuine new comparison is degree **1081 at
116 operations**, versus package 20's degree 1145 at 123 operations and
package 21's degree 1353 at 116 operations. The three-equation form has
maximum degree 1072 at 111 operations.

This audit checks the new algebra, the unbounded root-recovery argument,
the degree proof, and arithmetic accounting. It does not independently
prove the machine-to-native-window compiler or the K215/refutation endpoint.
All consistency claims continue to depend on those expressly identified
mathematical lemmas and on one complete authenticated coefficient tuple.
No claim of a kernel-checked Lean or Rocq theorem is made.

## Fair operation-count comparison

The new system emits its final norm equation as `N00 = GN11`, deleting the
otherwise unnecessary gate `N = N00 - GN11`. This is valid under the
repository's convention that equality comparisons are free. Exactly the
same rewrite applies to package 21's 112-operation norm12 system and makes
that existing system a 111-operation system. Consequently 111 is a fair
normalized count for both. The reduction in degree is substantive; the
one-operation decrease from a raw upstream count must not be advertised
as an exclusive operation-count breakthrough.

Independent DAG inspection confirms 12 live witness ports and four live
fixed ports, with no unused gates. The three main costs are:

| Form | Gates | Multiplications | Additions/subtractions |
|---|---:|---:|---:|
| Direct-comparison system | 111 | 72 | 39 |
| Product equation | 116 | 74 | 42 |
| Sum of squares | 119 | 75 | 44 |

## Bootstrap and weights

The weak transport argument needs to be applied before reconstructing any
root. For the product, parity first gives the common unit sign
`Nk = Nt = epsilon`; it does not assume that either sign is positive.
The inherited positive-coordinate estimates supply

    q >= 16, X >= q, Y >= q^3 >= 4096,
    3q < R < q^4 - 2, E >= q^4 > R+2,
    k = R + epsilon + hE > E, k > R,
    kY < c < k(Y+1) < 2kY.

In particular `A0 = a+2 < 2E`, and `k > 64`. These estimates are enough
for every subsequent bound and do not use a recovered Pell index.

For `M0 = k I^2 + T^2`, the two AM-GM bounds
`M0^2 >= 4k I^2 T^2` and `M0^2 >= k^2 I^4` separately show

    A M0^2 > 16 D v^2,
    A M0^2 > 16 b^2.

Indeed `A > A0^2 c^2/16`, `A > 64 A0^4`,
`D < A0^2 I^2`, and `b < 2k A0^2 I^2` follow directly from the displayed
bootstrap. Adding the separate inequalities yields
`A M0^2 > 8(Dv^2+b^2)`. Since `d >= Q/2` and
`M=(kI+T)^2 >= M0`, this proves the required strict inner inequality

    d A M^2 > 4Q(Dv^2+b^2).

The proof's outer separation bound is also valid. It can be strengthened
and shortened as follows. Since `Delta > (a+1)^2`,

    sqrt(G) > (a+1)c > (E+Y+1)kY.

For `ell=EkY`, the identity

    (ell+k/2)^2 - A = k^2/4 - 1 > 0

gives `sqrt(A) < ell+k/2`. Therefore

    sqrt(G)-sqrt(A) > k(Y^2+Y-1/2) > kY^2.

This is stronger than the proof's sufficient `kY^2/8` bound. That weaker
bound, together with the given auxiliary estimate and `Y>=4096`, already
proves `|y| < M(sqrt(G)-sqrt(A))` uniformly for every complex branch.

## Norm zero really recovers coherent integer roots

The formal-radical notation denotes a finite polynomial norm. It is not an
additional quantified root condition. Factoring the inner polynomial gives
the coherent branches

    x=M tau+y, tau^2=A, f^2=D,
    d y^2=Q(vf-b)^2-1.

Their uniform absolute bound is `|x| < M sqrt(G) < L sqrt(G)/H`.
If `G` were nonsquare, vanishing of the outer norm over the rational
coefficient field would force both conjugate factors to vanish. Their
corresponding roots differ by `2L sqrt(G)/H`, contradicting the bound.
Thus the recovered main root `u` is an integer. It is positive because
`S=b0+Hr>0` and the same bound excludes the negative branch.

For the now rational `x=(S-Lu)/H`, the inner estimate gives
`C(x)>Baux sqrt(D)>0` and `F(0)>0`. Therefore each denominator in the
displayed rational recovery formulas is nonzero. They yield rational
`f,tau` with integer squares `D,A`, so both are integral. The resulting
rational `y` is integral by the special rational Pell saturation lemma;
one cannot replace that lemma by the false general assertion that a
rational square root after dividing by `d` is integral.

Finally `L=1 mod H` gives the exact main congruence `u=b0 mod H`.
The first Pell equation and `k>R>48` imply `c>X`. Then
`u>(a+1)c` implies `(u-ac-X)/H>0`, recovering positive gamma. The only
possible sign adjustment left is `f,T -> -f,-T`; the inherited
signed-quotient normalized interface explicitly permits signed T.
This is a coherent restoration of the whole source certificate.

Completeness uses the exact polynomial identity

    r=gamma+M(u+tau)+y,
    b0+Hr=(1+HM)u+H(M tau+y).

All terms in the canonical witness are positive, so this introduces no
new unattested sign or divisibility condition.

## Product finalizer

In the scalar-norm circuit, `V1` is even, `C1` is even,
`Cs1` is divisible by 4, `Kc1` by 8, `W1` by 4, and `N1` by 8.
Thus `N=N0^2 mod 64`. An integer zero of `Nk Nt(1+N)-1` makes its
three factors units. The congruence excludes `1+N=-1`; therefore
`N=0` and `Nk=Nt=epsilon`. This establishes the weak-sign hypotheses
used at the beginning and avoids circular use of root recovery.

## Uniform exact degree, independent of coefficient expansion

Let `q0=beta J` and `k0=eta+zeta`. The highest-degree forms are

    H_top = 4 w s q0^4,
    Q_top = i^2 k0^4 w^4 s^8 q0^28,
    D_top = i^2 k0^4 w^2 s^6 q0^20,
    R_top = q0^3(q0-F),
    b_top = i^2 k0^4 w^2 s^6 q0^23(q0-F),
    e_top = i^6 k0^12 w^8 s^20 q0^74(q0-F)^2.

The term `-H^2 e` uniquely dominates `C0`, of degree 134. It propagates
through the unique largest square at every subsequent stage. Hence

    N_top = (H_top^2 e_top)^8
          = 2^32 i^48 k0^96 w^80 s^176 q0^656(q0-F)^16,

of degree 1072, while the competing final term `G N1^2` has degree at
most 1000. The nonzero expression remains nonzero for every fixed beta>0.
The product leading form is its product with

    -h w s q0^4 [w(q0-F-alpha)-z q0].

Its coefficient at `J^677 h z i^48 eta^96 w^81 s^177` is
`2^32 beta^677`, uniformly positive. Thus the product's exact degree is
1081. The sum of squares has unique largest summand `N^2`, hence exact
degree 2144.

`audit_hybrid12.py` independently checks gate dependencies, liveness,
costs, output comparisons, and 32 exact integer evaluations of these
highest-degree forms. Those finite checks support the algebra; the
uniform proof above supplies the degree assertion for the actual huge
fixed coefficients.
