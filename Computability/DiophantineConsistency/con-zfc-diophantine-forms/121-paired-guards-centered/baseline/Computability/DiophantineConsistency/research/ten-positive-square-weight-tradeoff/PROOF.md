# Reuse the existing strong-ordinate square as the transport majorant

The complete graphs zero97.json and direct102.json start from the sealed
index-weight zero98/direct103 equations. Keep all ten strictly positive
inputs, each complete coherent four-port tuple, the entire arithmetic
kernel, carrier and35-coefficient weighted norm. Replace only

    Lindex=kI+b   by   Lsquare=I²+b.

The source already computes I2=I*I for the strong norm. Delete the private
kI product and use I2 in L. This removes exactly one multiplication, with
no insertion. The actual graphs have97 operations (57 multiplications,
22 additions,18 subtractions) and102 operations (60/23/19). Their exact
degrees are368 and344, respectively, proved below. This is an operation/
degree tradeoff relative to98/360 and103/332, with no canonical change.

## 1. Complete changed center and pre-transport dominance

Use every unchanged definition and ordinary interface of the sealed
index-weight PROOF.md. In particular k=eta+zeta,c=kY+eta,I=i*c²,
A=mu*Y*(X+1)+1,H=4A-5,b=c(T+alpha)-R. The zero carrier has
g=q-1,B=Bt,X=wq,D=0; direct hasg=q(q-1),
B=(qK0+X)(q-F-alpha)-qF,X=q+x,D=(q-1)X. In both

    Wsquare=1+g*Lsquare, P=q³g, M=P*mu²*H,
    Z=P*mu²[H(n+V-Lsquare*B)+Kpos]
        +H[mu²(gY-q³B-D)-P*e].

Thus the exact rational proof identity is

    Z/M=n+V+Kpos/H+Y/q³-Wsquare*B/g-e/mu²-D/P.

DirectD/P=X/q⁴. Actual evaluation uses integer binary arithmetic only.

Every prerequisite to the sign argument is unchanged and independent of
L: positivity/noncancellation of the weighted roots(3tau,f,y), integral
root recovery, strong/auxiliary folding and the first-Pell classification.
They recover c=psi_A(p) for positive odd p, the first index n0>=2, and

    c>kY>=k>=8X(muY)²+4>H.

The last inequality is explicit before transport: for r=muY>=1,

    k-H>=4r(2Xr-X-1)+5>0,

since X>=32. Since i>=1,c>k>=2, the definition gives

    I>=c²>k, hence I²>kI>HI.

No transport divisibility, q parity, canonical value of a root or hidden
lower bound on the input i is used. In particular Lsquare>Lindex>0 at
the exact stage where the old proof excludes a negative carrier.

## 2. Complete ordinary soundness

The recovered signed-root center is

    n=eps1*3tau+eps2*f+(eps3*y-V)-Kpos/H-Y/q³
        +Wsquare*B/g+e/mu²+D/P.

The inherited pre-transport inequalities give3tau+f<kI in zero and
3tau+f+X/q⁴<kI in direct; both are now strictly less than I².
Also b>0,0<y-V<b/2 and |e/mu²|<b/2 while the latter is still rational.
If B<=-1, then Wsquare*B/g<-Lsquare. Dropping the negative Kpos/H and
Y/q³ terms gives n<I²+b-Lsquare=0 in either family, contradicting n>0.
Thus B>=0 without assuming its divisibility or source meaning.

The literal carrier forces C>0 and the same3q<R<q⁴-2 bounds. The unchanged
strong rank gives p=R before parity. Odd p then gives q even and J odd;
only afterward isolate mu²|e by carrier coprimality. The first-index
congruence gives n0=(R+1)/2, and the accepted zero-offset ratio estimate
supplies the height bound before whole-product projection. The integral
center yields H|P*Kpos, the old universal projection bounds its entire
product, and X=2^R follows before any nonunit factor is cancelled.

The only later requirements on the weight are integrality and Wsquare=1
modulo the transport factor. Both hold because Wsquare=1+gLsquare.
Consequently q³|Y and(q-1)|Bt are recovered at the same late step. In
direct, q|X and then q⁴|X are recovered AFTER removing H, before introducing
w=X/q or removing X/q⁴. No direct-base divisibility is assumed early.
The fixed-minus parity, exact half-binomial rounding, fresh prescribed
unscaled source and native/controller contracts then give a finite syntactic
refutation exactly as in the sealed proof. Private source and kernel
interfaces remain unchanged. The proof is uniform for each whole original
or BFS compact44 tuple; their distinct K0 values are not identified or mixed.

## 3. Positive completeness and a universal polynomial shear

Take ANY positive zero of the sealed index-weight parent. Its ordinary
soundness supplies B>=0, and its preceding first-index argument supplies
I>k. Put

    dL=I(I-k)>0, n_square=n_index+dL*B.

This is a positive integer, including B=0. Every other positive input and
kernel value is unchanged. The weight difference is g*dL, so

    n_square-Wsquare*B/g=n_index-Windex*B/g.

All normalized centers and complete norm arguments therefore agree.
More strongly the actual cleared center identity under this triangular n
shear is universal over the integer polynomial ring, independently of its
sign hypotheses. M and all three kernel radicands are independent of n.
The source checker recollects both actual graph centers and verifies that
identity coefficient by coefficient. Therefore every parent positive zero
has the displayed positive new zero; finite refutation completeness follows.

The inverse polynomial shear need not preserve positivity on arbitrary
new zeros. Soundness in Section2 proves its own transport sign and invokes
unchanged arithmetic contracts, rather than assuming such an inverse.
This establishes both ordinary positive-solvability implications, without
a new Lean or internal-ZFC theorem.

## 4. Exact changed degrees and complete leading forms

The actual source still has syntactic degree416 (zero),384 (direct).
The new L has degree10 in both. Its proof weight has degree11 or12.
The actual centered numerator Z0=Z-MV has degree25 in BOTH families.
Writing s=delta*Z² and h=M²*Dnum, the exact cancellation is

    omega=s-h=delta*Z0²+2delta*Z0*M*V-M²(V²-1).

Here deg delta=30/26,deg MV=37/35 and deg V=24/22. The three summands
have upper degrees80/92/74 or76/86/70, respectively. Thus the unique top
is2Q0*Z00*M0*V00, of degree92 or86. In the centered norm bracket

    E=omega²-2(u+v)(2h+omega)+(u-v)²,
    N=E²-64*(h+omega)*h*u*v,

u=9delta*M²Dtau has degree74/68,v=delta*M²Df degree76/70,h degree104/96.
Hence E has unique top omega², of degree184/172: the competing -4vh has
only degree180/166. The final product has degree at most358/330.
Therefore the complete N has unique top omega0^4, degree368 or344.
This differs from the parent index-weight case, where16v0²h0² controlled
the full degree.

Use q0=beta*J,k0=eta+zeta,c0=k0Y,I0=i*k0²Y²,C0=q0-F-alpha.
For zero let X0=wq0; for direct let X0=q0+x and
B0=(q0K0+X0)C0-q0F. The unchanged leading components are

    A0=q0²X0Y, Delta0=A0², Df0=Delta0*I0²,
    Q0=Delta0²*I0², R0=q0³(q0-F), V00=-Df0*R0,
    M0=4q0^10X0Y (zero) or4q0^11X0Y (direct).

The actual transport-leading centered term is

    Z00=-H0*q0^4*q0³*g0*I0²*B0,

where H0=4A0,g0=q0 orq0², and zeroB0=wC0. Thus direct multiplication gives

    zero omega0=2^5*q0^43*w^9*i^6*Y^20*k0^12*C0*(q0-F),
    direct omega0=2^5*q0^37*X0^8*i^6*Y^20*k0^12*B0*(q0-F).

Their full fourth powers are the complete homogeneous leading forms.
The original coefficient at J^172*w^36*i^24*Y^80*eta^48*alpha^4*F^4 is
2^20*beta^172>0. In direct the coefficient at
J^148*x^36*i^24*Y^80*eta^48*alpha^4*F^4 is2^20*beta^148>0.
The respective exponents sum to368 and344. Highest x^36 uniquely chooses
the X0^4*C0^4 part of B0^4, alpha^4 chooses all four C0 factors, and
F^4 then comes from(q0-F)^4. There is no leading cancellation or sampled
line-degree assumption. The complete symbolic leading forms are checked
against the actual graph front components.

## 5. Literal and verification boundary

The complete maps account for every parent row in order: delete only kI,
replace only L's operand by the already present I2, retain every other row
and metadata port. All remaining gates are live. All35 actual norm tail
coefficients, the eight-conjugate identity and the complete centered
cancellation are collected independently. Every compressed AND raw fixed
coefficient payload is pinned and checked as a coherent tuple. The actual
center identity under the positive-old-zero shear is verified universally.
Normal and optimized rebuild/check receipts, private-artifact corruption
controls and a closed manifest accompany this ordinary proof.

The previous LEAD.md records the historical prospective calculation; this
proof and the complete new graphs supersede its unmaterialized status.
No frozen parent, canonical page, common report, Lean file or Git commit
is changed by this research packet.
