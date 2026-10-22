# Final article audit: coefficient compiler and retained system

Reviewed `output/con_zfc_synthesis/con_zfc_synthesis.tex`, coefficient
section as present on 22 October 2026, against `research/strict_compiler.py`,
the strict window list, and the independent predicate/support audit.

## Coefficient section

All literal values and definitions agree:

* k=5252, alphabet size439, ell13, clause base2^13.
* Radix2^78125, cell length1953125, base2^(5^16).
* Copy offsets8764,8325,7886,7008.
* Dummy positions10520,10521; support size7014.
* Anchors11839,35517,59195,130229.
* mu=(2^13)-2+sum_{j=1}^{2835}(2^13)^j.
* Clause exponents1+l,440+c,879+r,1318+n; anchor exponents1757..1760.
* DC bare exponents1317,226698,47356,94712; bands487157,747619.
* DR exponent226259.
* MF center interval8325..8763, spatial intervalsHc+8764..9202 and
  Hc+8325..8763, target anchors59195 and130229, and source marker4.
* MC omits selector1 and allows one upper bit at dummy10520 only.
* The supplied MF port is shifted by Bbase-1.

The strict-language subset and padded-halt arguments are sufficient for
the old local-language interface. The literal support/target checks,
population count, rotation separation, carry estimates and modulo-five
unit are the same hypotheses used by the old native compiler. No new
divisibility/coprimality hypothesis on the cyclic stride is introduced.

For completeness of the prose, root was asked to add the elementary
mask bounds/congruences explicitly: the cleared MC bits are distinct and
leave unused high bits; MF's disjoint fields leave unused high bits too;
MC's low bit0 is removed while bit1 remains, and MF has only the native
marker4 below the first radix place. Thus0<MC,MF<Bbase-1,
MC=2 mod4 and MF=4 mod8. These statements follow from the displayed
recipe and are not extra assumptions.

## S59 section replacement essentials

The known erroneous draft S59 section was not edited or approved by this
audit. Its correct replacement must use exactly these sixteen positive
variables:

    J,F,alpha,z,f,h,i,o,j,s,w,tau,eta,zeta,y,gamma.

There is NO supplied T. Use the common q,C,X,Y,E,k,c,a,H,Delta,G,R,L0,
and define

    Dmain=X+a*c+gamma*H,
    V=o*f-c, U=j*c-R, I=i*c^2,
    Aaux=Delta*(f^2-1).

The seven equalities are

    tau^2-L0*(L0+k)=1,
    Dmain^2-Delta*c^2=1,
    Aaux*(V^2-y^2)+y^2=1,
    k-h*E-R=1,
    (K0+w)*C=F+z*(q-1),
    I^2=Aaux,
    U=V.

Here z=z_old-1; the old source proves z_old>=2 at positive solutions.
The old transport equality and the new one are identical under
z_old=z+1. The retained o,j source already has the two auxiliary minus
congruences, so it needs no T coordinate or additional T equation.

`RETAINED59_PROOF.md` and the emitted circuit agree exactly on these
formulas and variables. Their count is59 operations=33 multiplications
+26 additions/subtractions. Exact residual degrees are
22,18,24,7,2,22,6. The auxiliary coefficient Aaux should be named
distinctly from the first Pell radicand A and the sequence parameter a+2.

## Proof boundary

The coefficient theorem is an ordinary mathematical adapter proof using
the inherited native compiler and Pell theorems. The finite checks verify
the changed data and algebra; they do not create a new kernel-checked
bridge. The article's stated distinction between ordinary formalizability
in ZFC and a freshly checked Lean/Rocq theorem is appropriate.
