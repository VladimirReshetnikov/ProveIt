# Primitive odd carriers: fourteen integers at degree 86 / 112 operations

## Scope and dependency boundary

Four complete fixed integer-polynomial DAGs accompany this note. The new
`integer14_degree86_ops112.json` strictly improves the preceding fourteen-variable
88/119 point in degree and operation count. The new 94/110 point trades eight
extra degrees for two fewer operations. The 88/115 and thirteen-variable 156/125
companions are pointwise-identical recompilations of the retained old equations.
The 88/115 point is dominated by the new 86/112 point but records the exact
compiler-only saving. This is not a global optimum claim.

All six fixed integer numerals are copied unchanged in baseline/coefficients/;
MF is already shifted. The immediate fifteen-variable parent is
baseline/source/free_scale15_equation.json, proved in
baseline/source/FREE_SCALE15_PROOF.md. Its signed Pell, source34/native compiler
and syntactic-refutation calibration are inherited, not reproved by a finite
DAG test. The complete original source packet is retained in the containing
release. Our maps restore a literal zero of that parent, with no new canonical
witness requirement. Thus its ordinary ZFC-provable equivalence between integer
zero existence and finite syntactic ZFC refutability transfers. No consistency
proof, new object-language certificate or end-to-end Lean theorem is asserted.

## 1. Common complete arithmetic front

Use the parent's six fixed constants beta,K0,MC,MF,cone_A,cone_B. In particular
beta=2^1064921-1, cone_A=2^1113 and cone_B=2^666104. All names below are
polynomial abbreviations, not further quantified variables:

    J=6j+1, qm=beta J, q=qm+1, W=12w+4, X=qW, Y=v,
    F=(K0+W)C-z qm,
    R=(q(q-F)-C)(q²-1)+(MC+q MF)J,
    E=XY, a=E+Y, H=4a+3, Delta=a²+H,
    k=R+1+hE, eta=c-Yk, L=E(Yk), I=(2r+1)c²,
    q3=q³, M=2q3, U=MH, Klo=X(2X-3c)-2,
    Z=Un+M Klo+H(Y-q3),
    Derr=(cone_A F-q)²+(cone_B C-q)²,
    budget=(Yk)²(q²-Derr)-q²[4(Y eta)²+(kq3)²],
    Acar=(Z+Uk)²+4U(LZ-U).

The fifteen-variable parent additionally has f,y,p1,p2,p3 and uses

    Q=Delta(f²-1), V=f²(cT-R)-c,
    Bstrong=f²-Delta I²-1,
    Caux=V²-(Q-1)y(2V+y)-1,
    Bguard=budget-1-p1²-p2²-p3(p3+1).

Its equation is Acar²+Bstrong²+Caux²+Bguard²=0. It is therefore exactly the
simultaneous vanishing of these four integer residuals.

Unconditionally, q is even and nonzero: beta is odd and beta>1, so beta J=-1
is impossible. H is odd and nonzero, and U is nonzero. Also |W|>=4 and
|X|>=8. Since a=(X+1)Y is zero or |a|>=7,

    Delta=(a+2)²-1 >=3.

These facts precede all root extraction. The old norm Acar is a square modulo4,
so Acar != -2. For every integer A0=a+2, Delta=A0²-1 is either0 or3 modulo4.
Since I² and f² are0 or1 modulo4, Bstrong is0,1 or3 modulo4 and is not -2.
No sign or source equation is needed for either exclusion.

## 2. The exact primitive odd-carrier lemma

Let b,d,e,s be integers with d nonzero. Put G=4b+1 and

    K=d(s(s+1)-b)-e, N=K²-Gde.

Then N=0 if and only if there are integers g,u such that

    g²=G, d u²=e, 2s+1=g+2u.

This assertion is valid for signed d and e; it makes no real-root assumption.
Put x=2s+1, which is nonzero. The exact polynomial identity

    16N=[d(x²+G)-4e]²-4d²x²G

shows that at N=0 the rational number

    g=[d(x²+G)-4e]/(2dx)

satisfies g²=G. A rational number with integral square is integral (in a
reduced fraction, its denominator square divides its coprime numerator
square). Since G=1 modulo4, g is odd. Consequently u=(x-g)/2 is integral.
The defining equality for g and g²=G give d(x-g)²=4e, hence du²=e.
Conversely these equations give N=0 by direct substitution. In particular
G cannot be negative at a zero; neither a zero carrier nor an irrational
cancellation branch is silently discarded.

This elementary identity is the primitive two-root merger already present
in the retained parity-norm literature. The new construction is its exact
placement at the free-scale auxiliary/triangular interface and its tailored
unit-product finalizer, not a priority claim for the generic identity.

## 3. Principal fourteen-variable equation: degree 86

Take the fourteen unrestricted integer unknowns

    j,C,z,h,r,v,w,T,c,n,f,p2,p1,s.

Use the common front and Q,V above, but no y or p3. Define

    B=budget-p1²-p2², G=4B-3,
    delta=Q-1, Cy=QV²-1,
    K=delta(s(s+1)-B+1)-Cy,
    N=K²-G delta Cy,
    Sunit=f²-Delta I²,
    P86=(Acar+1) Sunit (N+1)-1.

This is the literal division-free polynomial in the principal JSON file.
Suppose P86=0. The three integer factors multiply to1, so they are units.
The first cannot be -1 because Acar!=-2. The second cannot be -1 because
Bstrong!=-2. Both are therefore+1 and then N+1=+1. Thus

    Acar=Bstrong=N=0.

The strong equation gives Q=Delta²I². This is0 or at least9, so delta is
nonzero. Apply Section2 with b=B-1, d=delta, e=Cy. It yields integers

    g²=G, delta u²=Cy, g odd.

Restore the deleted parent variables by

    p3_old=(g-1)/2, y_old=u-V,

leaving every other parent input unchanged. The guard is zero because
p3_old(p3_old+1)=(G-1)/4=B-1. Moreover

    Caux_old=QV²-(Q-1)(V+y_old)²-1=Cy-delta u²=0.

Thus every new zero gives a literal parent zero. The case I=0 gives
Q=0, delta=-1, Cy=-1 and is included in the same argument; no positive-Pell
or nonzero-c premise has been used here.

Conversely take any parent zero, retain all common inputs and f, and put

    s=p3_old+V+y_old.

With g=2p3_old+1 and u=V+y_old one has g²=G, delta u²=Cy and2s+1=g+2u.
The lemma gives N=0. The other two unit factors are1, hence P86=0. This
polynomial lifting works for every parent zero, not merely canonical ones.
All proof-only divisions in soundness have separately established integer
values. Consequently the existence equivalence uses no new number-theoretic
existence or simultaneous Pell interpolation hypothesis.

## 4. Lower-cost companion: degree 94

Use fourteen unrestricted inputs

    j,C,z,h,r,v,w,T,c,n,y,p1,p2,s.

Replace the eliminated f² everywhere by

    Ds=Delta I², Fs=1+Ds, Q=Delta Ds, V=Fs(cT-R)-c.

Keep B=budget-p1²-p2², G=4B-3 and define

    K=s(s+1)-B-Ds,
    N=K²-G Fs,
    Aunit=V²-(Q-1)y(2V+y),
    P94=(Acar+1)(N+1) Aunit-1.

Here Fs is positive unconditionally. Also Fs is0 or1 modulo4: Delta is
0 or3 modulo4, and I² is0 or1. Since G=1 modulo4, N is0,1 or3 modulo4,
so N!=-2. Acar!=-2 was already proved. The integer unit-product argument
therefore gives Acar=N=0 and Aunit=1 at every zero of P94.

Apply Section2 with b=B-1, d=1, e=Fs; its K is precisely the displayed K
because Fs=Ds+1. Obtain odd g and integer f with g²=G and f²=Fs.
Set p3_old=(g-1)/2 and restore f_old=f, leaving the other parent coordinates
unchanged. All four old residuals vanish. Conversely from any parent zero
set s=p3_old+f_old and delete f_old,p3_old. The primitive identity gives
N=0 and the other retained rows vanish. These are again maps on every zero.

## 5. Exact-polynomial compiler companions

The old 13/156/127 evaluator formed Caux=Eaux-1 and later Caux+1. Forming
Eaux directly removes both operations, leaving an exactly identical output
polynomial in125 operations. The old14/88/119 evaluator also formed
Bstrong=Estrong-1 and then Bstrong+1. Removing both pairs leaves the same
polynomial in115 operations. No degree, coefficient, zero set or proof
premise changes. The checker binds the old and new cuts and final identities.

## 6. Exact fixed-coefficient degree and costs

Let the highest forms of the common front be

    q0=6 beta j, X0=12q0 w, Y0=v,
    R0=q0^4 z-12q0^3wC, a0=X0Y0,
    U0=8q0^3X0Y0, L0=X0Y0²R0,
    Z0=U0 n+4q0³X0².

One has degree(Acar)=22 and its top form isU0²R0²+4U0 L0 Z0; degree(budget)=18
with top form -R0²q0^8.

For P86, degrees Q,V,Cy,K,N are8,7,22,26,52. The degree52 norm top is

    N52=a0^4 f^4 R0^4 q0^16,

because G delta Cy has degree48. The degree12 strong-unit top is
-4a0²r²c^4. The unique degree86 output part is their product with Acar22.
Its actual nonzero coefficient is

    [j^51 w^9 v^10 z^5 f^4 r² c^4 n] P86
        =-2^79 3^60 beta^51.

For P94, degrees Fs,Q,V,N,Aunit are12,18,17,36,36. Its norm top is
R0^4q0^16; its auxiliary-unit top is32a0^6r^4c^8R0 y. The degree94 part is
again the unique product of three top forms. The actual coefficient is

    [j^55 w^9 v^10 z^6 r^4 c^8 y n] P94
        =2^86 3^64 beta^55.

Both exponent sums equal the asserted degrees and the actual beta is nonzero.
Thus these are exact degrees at the authentic numeral tuple, not generic-port
estimates. The inherited nonzero witnesses for88 and156 are unchanged.
The literal live binary operation counts (multiplication/addition/subtraction)
are86:64/22/26=112,94:63/23/24=110,88:67/25/23=115,
156:75/26/24=125. All variable and fixed-coefficient leaves are live. These
are arithmetic-DAG lengths, not bit complexities.

### Inherited leading-form erratum

This is the already-disclosed correction in the retained
KNOWN_LEADING_FORM_ERRATUM.md (upstream commit683470327943e1783dc1116c29488161559a7364),
not a new defect discovery. The retained FREE_SCALE15_PROOF.md Section8 omits U0²R0² from its stated
complete degree22 carrier form: (Z+Uk)² contributes this term. The correct
complete form is the one just printed. Its old n² coefficient and the new
n-dependent degree witnesses remain unchanged, since the omitted term is
n-free. No signed-Pell or zero-set argument depends on that omission. The
checker propagates the whole actual DAG leading form, rather than trusting
the incomplete printed expression.

## 7. Finite verification versus mathematical dependency

The independent checker does not import the builder. It checks each named
register against separate expanded formulas, topology, liveness, all literal
counts, complete leading forms and the selected fixed-coefficient monomials.
It proves the primitive merger, reconstruction and lift identities in a free
polynomial ring, exhausts the relevant finite residue cases, authenticates
all numeral/source bytes, verifies old/new exact-output identities and
rejects a separate mutation at every arithmetic gate. The same acceptance
conditions run with Python -O. A deterministic rebuild reproduces all DAGs.
These checks establish finite algebraic transcription and metrics. They do
not decide existence of a zero or prove the inherited unbounded native theorem.
