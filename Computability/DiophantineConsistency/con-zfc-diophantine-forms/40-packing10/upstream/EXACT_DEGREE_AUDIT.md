# Exact degree of the B2 source with the inherited ten-integer finalizer

This audit treats every fixed coefficient as degree zero and the ten
supplied unrestricted variables as degree one. It assumes the finalizer
formulas of package 31's structural three-square construction are retained.

Let t=799, E_max=44t+21, M=46t+21, and u=M+t+2=47t+23=37576.
The new base B=beta*b^2 has degree two. Its source polynomial D has exact
degree 2E_max because the final row's constant coefficient is nonzero.
The geometric sum in J has degree 2(M+1), strictly exceeding the degree
2E_max+2 of 2(1+g)^2D. Thus there is no cancellation of J's leading term.

The source degrees are

| Expression | Exact degree |
|---|---:|
| b | 1 |
| B | 2 |
| D | 2E_max |
| N0 | 2(t+1) |
| N1 | 2(M+1) |
| N | 2u |
| J | 2(M+1) |
| S | 2u |
| T | 2(E_max+t+2)=2u-4t |
| R | 4u |
| X | 6u=225456 |
| Y | 4u=150304 |
| cap | 2t+1=1599 |

The strict inequality deg(S)>deg(T) establishes the next two lines; all
other source highest-degree terms have nonzero coefficients.

For checking a rebuilt finalizer, write x=deg(X), y=deg(Y), c=deg(cap).
These symbols denote degrees, not the finalizer variables. Direct
propagation with strict dominance gives:

| Expression from package 31 | Exact degree |
|---|---:|
| L=lY | y+1 |
| U=2LX | x+y+1 |
| V=4gwY | y+2 |
| W=bw | 2 |
| A=U(V+1) | x+2y+3 |
| B_small=2X+1 | x |
| C=B_small+(A-2)h | x+2y+4 |
| P_n=U^2V | 2x+3y+4 |
| K=X+1+k(P_n-2) | 2x+3y+5 |
| S_small=2A-5 | x+2y+3 |
| T_small=3WC-2(W^2-1) | x+2y+6 |
| R2=(P_n^2-4)K^2+4 | 8x+12y+18 |
| Delta_bridge | 4x+8y+3c+14 |
| O=f^2l^2 Delta_bridge | 4x+8y+3c+18 |
| r0=b(1+(3O-4)b^2z^2) | 4x+8y+3c+23 |
| D_lucas=(A^2-4)C^2+4 | 4x+8y+14 |
| E_lucas=C^2 D_lucas zx | 6x+12y+24 |
| F_lucas=4(A^2-4)E_lucas^2+1 | 14x+28y+54 |
| Gstar=2(A+2)(A-2)^2 E_lucas^2-1 | 15x+30y+57 |
| Omega=16E_lucas | 6x+12y+24 |
| Hstar=C+(B_small-C)F_lucas+Omega F_lucas y_var | 20x+40y+79 |
| Istar=(Gstar^2-1)Hstar^2+1 | 70x+140y+272 |
| r1=R2 | 8x+12y+18 |
| r2=D_lucas F_lucas Istar | 88x+176y+340 |
| Sigma=zx S_small^5 | 5x+10y+17 |
| Theta | 5x+10y+30 |
| norm_center=Sigma m-Theta | 5x+10y+30 |
| scaled_A0=Sigma^2 r0 | 14x+28y+3c+57 |
| scaled_A1=Sigma^2 r0^2 r1 | 26x+48y+6c+98 |
| scaled_A2=Sigma^2[r0(P_n^2+K^2+3)]^2 r2 | 114x+224y+6c+440 |

For the bridge discriminant, the highest part is the negative term
-32 g^2 cap^3 K^2 L^2. Its degree strictly exceeds the other terms. The
negative sign does not create a zero leading polynomial. For Theta the
highest part of T_small+S_small*y_var is T_small, so the quintic merger
has the fifth power of that nonzero leading part.

The degree d2 of scaled_A2 strictly exceeds those of scaled_A0,
scaled_A1, and norm_center^2. Therefore the nested three-square norm

    Vn = norm_center^2 + scaled_A2 - scaled_A0 - scaled_A1,
    Wn = Vn^2 + 4 norm_center^2 scaled_A2 - 4 scaled_A0 scaled_A1,
    F10 = Wn^2 - 16 Vn^2 norm_center^2 scaled_A2

has exact leading homogeneous part (scaled_A2_top)^4, which is nonzero.
Consequently

    deg(F10) = 456x+896y+24c+1760
             = 6320u+48t+1784
             = 297088t+147144
             = 237520456.

This is a symbolic proof of both the upper and lower degree bound. No
random specialization or numerical interpolation is needed. As a check,
substitution of the old source degrees x=120t+24, y=80t+16, c=4t+1 yields
126496t+27064, exactly the degree reported by package 31.
