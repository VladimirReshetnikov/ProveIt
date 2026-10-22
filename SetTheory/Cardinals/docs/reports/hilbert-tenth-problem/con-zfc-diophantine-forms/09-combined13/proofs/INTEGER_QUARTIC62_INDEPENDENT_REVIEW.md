# Independent review: the 32-variable quadratic system and 62-integer quartic

Reviewed sources: `low_degree/quartic32.py`, `LOW_DEGREE_PROOF.md`,
`SIGNED_CORE_AND_INTEGER62.md`, and `integer_quartic62.py`.
Imported arithmetic references were independently read at ProveIt
`3b201cdea32d2c816f5f3d20734051f25fd3ef14`: package02's
`PELL_INTERFACE_LEMMAS.md` and native-stream-queue's
`pell_kernel_half_binomial42.md`.

## Verdict

The 62-integer-variable quartic construction is mathematically valid under
the explicitly imported ordinary-strong Pell lemma and authentic blank
compiler theorem. Its signed-domain proof checks the needed signs and does
not apply a positive-tuple theorem to a signed tuple. No new proof-assistant
formalization is claimed.

## 1. Register projection and forced positivity

Impose positivity only on

    J,F,alpha,z,i,s,w,eta,zeta,gamma.

The other six primary coordinates and all sixteen registers may be signed.
The first seven quadratic equations force, in order,

    q=beta J+1>=B>=16,
    L=q^2-1>0, N=q^3>0, X=wq>0,
    Y=a-E=sN>0, E=XY>0, a=E+Y>0,
    k=eta+zeta>0, c=kY+eta>0,
    P=EkY+k>0.

Thus equation8 is precisely
tau^2-XY^2(XY^2+1)k^2=1. The positive geometric quantities force
H=4a+3>0, Delta=a^2+H=(a+2)^2-1>0,
D=X+ac+gamma H>0, and C2=c^2>0.
I=iC2>1 and Baux=I^2>1 also follow, without assuming register signs.

The transport equality forces C=q-F-alpha>0: for C<=0 its left side
is at most 1-F-(z-1)(q-1)<=0. Therefore F+C<q. Set R=jc-V;
the packing equation forces the exact authentic rank and the bounds

    (2q-1)(q^2-1)<R<q^4-q^3, E>=q^4>R+2.

The index equation is k=R+1+hE. If h<=-1, its right side is negative,
contrary to k>0, so h>=0. This is enough to obtain k>=R+1 and c>2R.
No positivity of the register V or the primary coordinates o,j is used.

## 2. Ordinary strong rank with signed f

Classify the first norm using |tau|, giving
k=2psi_P0(n), P0=2XY^2+1, n>=1.
Modulo E, 2n=R+1, with 0<R+1<E, implies n>=(R+1)/2>=24.
The positive main norm gives c=psi_A(p),D=chi_A(p), A=a+2.
Since P0>A and c>k, p>n. Consequently c>A Delta^2 and c>2p by
the usual elementary Pell growth estimates; also c>2R as above.

The strong equality is (ic^2)^2=Delta(f^2-1). Its positive left side
forces f^2>1. The ordinary-strong lemma applies to the positive number
|f|, with all its stated premises verified. It supplies

    |f|=chi_A(m), c|m, p|m,
    I=ic^2=Delta psi_A(m), m>=c>2p.

This does not assert that i/Delta is integral; no invalid normalization
of an arbitrary ordinary strong witness occurs.

## 3. Signed auxiliary rank

The last equations are exactly

    I^2 V^2-(I^2-1)y^2=1,
    V=of-c=jc-R.

Because I>1, neither V nor y is zero. Pell classification of
(I|V|,|y|) yields an odd index ell=2u+1. With epsilon=sign(V),

    V=epsilon Q_u(I^2),
    Q_u(0)=(-1)^u ell,
    Q_u(1-A^2)=(-1)^u psi_A(ell).

Oddness follows since I divides chi_I(ell), while even-index chi values
are +/-1 modulo I. Arbitrary signs of o,j,f preserve

    V=-c modulo |f|, V=-R modulo c.

Reduce the first congruence using I^2=-Delta modulo |f| and square.
The sign epsilon disappears and Pell doubling gives

    chi_A(2ell)=chi_A(2p) modulo chi_A(m).

The signed chi step-down lemma, applicable because 0<2p<m, gives
ell=+/-p modulo m, hence modulo c. Reduce the second congruence using
c|I and Q_u(0); this gives R=+/-p modulo c. Since 0<R,p<c/2,
only R=p is possible. The argument requires no sign for V,o,j,y,f.

Now write 2n=R+1+vE with v>=0. If v>=1 then 2n>2R, contrary
to n<p=R. Hence 2n=R+1 and R is odd. At this later stage even h>0
follows: n>=24 and P0>1 imply k=2psi_P0(n)>2n=R+1.

## 4. Essential qualification on the kernel citation

One must not invoke the complete positive half-binomial kernel theorem
verbatim at this point. Its separate necessity statement R=3 mod4
uses the positive fixed-minus auxiliary root; V here may be negative.
Instead use only the forward estimates in sections5-6 of
`pell_kernel_half_binomial42.md` (or the corresponding signed-quotient
scout sections). Their actual hypotheses are already available:

    c=psi_A(R), k=2psi_P0((R+1)/2), kY<c<k(Y+1),
    X>=q, Y>=q^3, R>3q, R<q^4, R odd,
    D-ac=X+gamma(4a+3).

The lower-ratio estimate and main-root congruence give X=2^R. Then
q|X implies q=2^t and R>3q>3t implies q^3|X. Under the restored
symmetric scale, the upper-ratio estimate and binomial expansion give

    Y=floor((X+1)^(R-1)/X^((R-1)/2))/2,
    v2(Y)=popcount(R)-2.

These extraction and valuation arguments use neither V's sign nor
R=3 mod4. They provide popcount(R)>=3t+2, which is all the exterior
inverse-population/mask decoding needs. The authentic coefficient
compiler then recovers a blank K215 halt. The reviewed signed proof
explicitly follows this restricted forward route, resolving the concern.

Completeness comes from the existing positive construction, so no new
signed converse and no new parity construction are needed.

## 5. Integer guard conversion and exact degree

Keep all32 core variables, and for each of the ten constrained primary
variables add three fresh integers and one equation

    x=1+u_x^2+v_x^2+w_x(w_x+1).

The right side is always positive on integers. It represents every
positive integer x by Legendre's three-square theorem applied to
4(x-1)+1, which is never of the excluded form 4^a(8b+7). Modulo4,
exactly one of the three representing squares is odd, producing the
displayed form. Thus these are exact positivity guards, without changing
the existential predicate.

There are32+30=62 integer variables and23+10=33 quadratic residuals.
The sum of their squares vanishes precisely when all equations hold.
Every residual remains quadratic because the positive primaries were
retained as separate coordinates rather than substituted into products.
Only residual8 contains tau, with coefficient+1 on tau^2. Consequently
the sum of squares has coefficient1 on tau^4 and exact degree4.

The source code's variable lists, counts and residual equations agree
with this argument. The proof concerns existential equivalence, not a
tuple-by-tuple identification with the all-positive32-variable system.
It combines with the cross or four-site coefficient recipes because
they preserve precisely the same authentic arithmetic/compiler interface.
