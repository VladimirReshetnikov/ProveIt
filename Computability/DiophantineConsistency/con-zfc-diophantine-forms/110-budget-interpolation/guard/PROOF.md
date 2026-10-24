# Twelve unrestricted integers by early rational projection

## 0. Result and inherited boundary

The late-arriving trace/interpolation precursor already proves early trace recovery and removal of the v-squared multiplier and enlarged main-root coefficient at thirteen integers, degree 1072 and 190 operations. Its proof is retained at `provenance/trace_precursor/TRACE13_PROOF.md`; no novelty for those individual devices is claimed here. The present construction combines that method with the centered-budget guard and a modulo-3 main-root projection.

This construction removes the nearest-square coordinate from the thirteen-integer CRT root-fusion endpoint. It combines the centered-budget guard with an early rational-squareclass projection of a vanishing norm factor. The projection restores the cubic scale before individual roots are known to be rational, then forces the main root to be integral by a fixed residue obstruction modulo 3. Thus neither the old v-squared guard multiplier nor the enlarged main-root coefficient is needed.

The proof applies to every signed integer input. Its soundness map targets the pinned normalized centered-budget17 source, not the stronger old determinant-guard source. Its completeness uses the authentic canonical source34 family and the prescribed half-binomial Y, not a freely adjustable Y.

The exact local ordinary proof interfaces are:

- `provenance/centered17/BUDGET_PROOF.md`, Sections 2–4, and `normalized17_degree48.json`;
- `provenance/centered18/PROOF.md`, especially Sections 4 and 6;
- `provenance/rootfusion/NORMALIZED_NORMS_PROOF.md`, especially Sections 2, 5 and 14.

SOURCE_PINS.json authenticates the copied files. Native/compiler, Pell rank and step-down, and finite-refutation calibration remain explicitly inherited ordinary mathematical theorems. No new kernel-checked endpoint, consistency proof, or global optimality claim is made. Exact degree and operation counts are separate circuit claims proved in DEGREE_PROOF.md and NORM_EVALUATOR_PROOF.md.

## 1. Complete definitions

Use the same six fixed source34/cone numerals beta,K0,MC,MF,cone_A,cone_B. In particular beta=2^1064921-1, cone_A=2^1113, cone_B=2^666104, and MF is already shifted. Supply exactly

    j, C, z, h, r, v, w, T, c, n, p2, p3 in Z.

Uppercase C and lowercase c are distinct. All other symbols are polynomial abbreviations:

    Jold=6j+1, q=beta Jold+1, W=4(3w+1), X=qW,
    Y=qv, E=XY, a=(X+1)Y, H=4a+3, Delta=a²+4a+3,
    F=(K0+W)C-z(q-1), alpha=q-F-C,
    R=(q(q-F)-C)(q²-1)+(MC+q MF)Jold,
    k=R+1+hE, eta=c-Yk, i=2r+1,
    Df=1+Delta i²c⁴, Q=Delta(Df-1)=Delta²i²c⁴,
    delta=Q-1, V=Df(cT-R)-c, Cy=QV²-1,
    L=XY²k, Dt=1+L(L+k), Dm=1+Delta c²,
    Derr=(cone_A F-q)²+(cone_B C-q)²,
    B=k²(q²-Derr)-4q²eta²,
    Ag=B-1-p2²-p3(p3+1),
    M=2q², U=MH, b0=X+ac,
    Z=U(n+V+S)+M b0+H(v-q²).

Here S=L gives the first-root-centered version; S=0 gives the auxiliary-only companion. More generally, any fixed integer polynomial S independent of n is an allowed integral carrier shear.

The packed R equals the original source expression because (q-1)(q-F)+alpha=q(q-F)-C. Let F32(Z;A1,...,A5) be the product over all 32 signs of Z-sum(ei sqrt(Ai)). This sign-invariant product is an integer polynomial, with degree at most 16 in each radicand. Define

    P12=delta^16 F32(Z; M²Dm, U²Df, U²Dt, U²Ag, U²Cy/delta).

The displayed denominator is fully cleared. The literal circuit uses only binary addition, subtraction and multiplication. For a denominator-free formal interpretation put d=M²Dm,e=U²Ag,A=U²Df,B0=U²Dt,C0=U²Cy, work in the free rank-four algebra u²=d,v0²=e, and set

    Rformal=Z+u+v0,
    Jformal=delta(Rformal²-A-B0)-C0,
    Kformal=Jformal²-4(delta² A B0+delta C0(A+B0)),
    Nformal=Kformal²-64delta³ A B0 C0 Rformal².

The four-conjugate product of Nformal is exactly P12. This identity remains valid when a specialized algebra is not a field. The optimized evaluator computes this same polynomial.

## 2. Unconditional realness and residue facts

Every integer input has q even, q=2 modulo 3, |q|>=16, and |X|>=64. Also X=2 modulo 3, so a=(X+1)Y is 0 modulo 3. Therefore

    H=0 modulo 3,       b0=2 modulo 3.

These facts require no guard or Pell equation.

If v=0 then a=0, Delta=3 and H=3. Otherwise |Y|>=16 and |a|>=1008. In both cases a is even, Delta is positive and odd, and H is nonzero. Since H=3 modulo q and q=2 modulo 3,

    gcd(H,M)=gcd(H,2q²)=1.

The denominator delta never vanishes. If c=0, Q=0, delta=-1, and Dy:=Cy/delta=1. If c!=0, Q>1 and Df>|c|+1. With the integer b=cT-R, V=Df b-c has |V|>=1, so

    Dy=V²+(V²-1)/(Q-1)>=1.

Df,Dm are positive, and Dt is positive because t(t+1)>=0 for every integer t, here t=XY². Thus all four non-guard radicands are positive on every integer input.

At P12=0, some complex norm factor vanishes. If Ag<0, its radical gives the only nonzero imaginary summand in that factor, impossible. Therefore Ag>=0 and

    B=Ag+1+p2²+p3(p3+1)>0.

It follows that q,k are nonzero and Derr<q², 4eta²<k². No v!=0 assumption or individual root rationality has entered this argument.

## 3. Integer rational projection

Lemma. Let A1,...,As be nonnegative integers, let t>=0 have rational square, and let aj,b be integers. Suppose every rational t allowed by the construction is integral. If sum aj sqrt(Aj)+bt is rational, it is an integer, even when irrational terms cancel.

Proof. Every positive rational-square radical is a positive rational multiple of a positive squarefree integer radical. Distinct squarefree radicals are linearly independent over Q. The rational sum therefore equals its squareclass-1 part. A rational sqrt(Aj) is an integer; a rational t is integral by hypothesis; all coefficients are integers. Irrational squareclasses contribute zero. Zero terms cause no exception.

The lemma applies here to y=sqrt(Dy). If c=0, y=1. If c!=0, Q>1 globally, and adjacent-coefficient descent proves that rational y satisfying

    QV²-(Q-1)y²=1

is integral. For clarity, if y=a/s in lowest terms then s² divides Q-1. The transformations

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV

preserve the norm, keep V' integral and preserve the denominator s. With positive signs and |V|>1, one has -|V|<V'<|V|; the norm excludes V'=0. Descent reaches |V|=1 and |y|=1, hence s=1. No decoded Pell index or native sign theorem is used.

## 4. Restore the scale and main root before separating the others

Let d,f,t,g,y denote nonnegative square roots of Dm,Df,Dt,Ag,Dy. A vanishing factor, with independent signs absorbed into their coefficients, has the form

    Z=M ed d+U(ef f+et t+eg g+ey y),       ei in {-1,1}.

Dividing by M gives a rational signed sum with integer coefficients, because U/M=H. The projection lemma implies Z/M is an integer. But

    Z/M=H(n+V+S)+b0+H(v-q²)/M.

Therefore M divides H(v-q²), and the unconditional gcd(H,M)=1 gives

    v_old=(v-q²)/(2q²) in Z,
    v=q²(2v_old+1),
    Y=(2v_old+1)q³.

In particular v!=0 and |Y|>=|q|³>=4096. This recovery precedes, rather than assumes, individual root extraction.

Next apply the squareclass-1 projection to the undivided factor. Every projected f,t,g,y term is an integer, by the same lemma's component argument. If d were irrational, its projection would be zero, so H would divide Z. Yet

    Z=M b0 modulo H,
    M b0=1 modulo 3,
    H=0 modulo 3,

a contradiction. Thus d is rational and hence integral. Let d_s=ed d. The same projection modulo H now gives H|M(d_s-b0). Cancelling the unit M modulo H proves

    gamma=(d_s-b0)/H in Z.

This recovers the actual signed main root and its congruence before any separation among the other four roots. Merely projecting the rational sum does not claim those remaining roots are already rational.

## 5. Four-root separation on every signed input

After early CRT put x=|X|,m=|Y|,K=|k|,Cabs=|c|. From the budget and c=kY+eta,

    x>=64, m>=|q|³>=4096, K>=1,
    K(m-1/2)<Cabs<K(m+1/2).

In particular Cabs>=16. No K>=2 assumption is needed. Direct elementary bounds give

    sqrt(Delta)>(x-1)m-3>3,
    K(xm²-1)<t<K(xm²+1),
    t>3Cabs,
    d>((x-1)m-3)K(m-1)>(3/4)t.

For the last inequality, the difference after multiplying by four is

    m²(x-4)-4m(x+2)+9>0;

already m>=16 makes (x-4)m-4(x+2)>=12x-72>0. Also

    f²-(Cabs²-1)d² >= (Delta-1)Cabs²+2>0,

so f>(Cabs-1)d>=15d>2t and f>3Cabs².

The unmultiplied guard is much smaller than c:

    g<|q|K,
    g/Cabs < |q|/(m-1/2)
              <= |q|/(|q|³-1/2) < 1/255.

The final inequality holds for all |q|>=16: 255|q|<|q|³-1/2 follows already from |q|²>=256 and |q|>1/2.

If b=cT-R=0, then V=-c and Q>Cabs²>1, hence

    Cabs<y<Cabs+1,
    y>g,
    y+g<Cabs+1+Cabs/255<3Cabs<t.

Thus f,t,y,g is strictly superincreasing, omitting g if zero. If b!=0, then |V|>=f²-Cabs>2f, so y>2f and y,f,t,g is strictly superincreasing.

Subtract the already integral main-root contribution from the factor and divide by U. It is a rational signed sum of f,t,g,y. Independence of distinct squarefree radicals and the strict superincreasing order force each root to be rational: the largest term of any nontrivial class cannot cancel the others. Then f,t,g are integers by their integer radicands, and y is integral by the same adjacent-coefficient descent. This proves all root recovery without circularity.

## 6. Pointwise map to the centered-budget17 source

Choose the signed roots f_s,t_s,p1_s,y_s in the original factor. Restore the source17 coordinates by

    J3=2j, f_source=f_s, v_scale=v_old, w3=w,
    tau_source=t_s-L, y_source=y_s-V,

keeping h,r,T,c,z and using F,alpha,gamma as defined or recovered above. The source has precisely the same k,R,eta,Delta and B. The six rows vanish:

1. The first is the integral translation of t_s²=1+L(L+k).
2. The main is d_s²=1+Delta c² with d_s=X+ac+gamma H.
3. Transport vanishes identically by F=(K0+W)C-z(q-1).
4. The strong row is f_s²=1+Delta i²c⁴.
5. Its V=f_s²(cT-R)-c equals ours, and its centered auxiliary row is the translation of QV²-(Q-1)y_s²=1.
6. Since Ag=p1_s², the budget row holds with B=1+p1_s²+p2²+p3(p3+1).

The centered source theorem supplies the calibrated finite syntactic ZFC refutation. This is not a pointwise map to the old determinant guard: B>0 need not imply that stronger determinant. The centered source's own signed-bootstrap and late half-binomial argument restore its original positivity guards.

## 7. Canonical completeness

Given the calibrated finite refutation, take the authentic canonical source34 family of the centered-budget theorem. Its repunit Jold is odd and is 1 modulo 3, so j=(Jold-1)/6 is integral. The prescribed half-binomial Y and native scale estimates give

    Derr<=q²/2,
    0<eta/k<1/4,
    B>q²k²/4>0.

These uniform estimates apply to that fixed canonical Y; no arbitrary large-Y choice is assumed. The normalized strong/auxiliary completion supplies integer f,t,y without changing native coordinates, k,eta,Y or B. Set v=Y/q=q²(2v_old+1).

Every positive integer N is represented by Pos=1+p1²+p2²+p3(p3+1): apply the three-square theorem to 4N-3, which is 1 or 5 modulo 8, then separate its one odd and two even squares. Represent B in this way, so Ag=p1². With canonical d=b0+H gamma choose

    n=gamma+f+t+p1+y-V-S-(v-q²)/M.

Every term is integral and direct substitution gives a vanishing norm factor. Thus P12=0.

Therefore the twelve-integer polynomial has a zero exactly when the same pinned calibration has a finite ZFC refutation. Under that inherited ordinary theorem, ZFC proves universal nonvanishing over Z^12 equivalent to Con(ZFC).

## 8. Integral shears, exact metrics and finite checks

For any integer polynomial S independent of n, replacing n by n+S is an integer-polynomial bijection on every fiber. The inverse subtracts S. Early CRT, the modulo-3 main-root obstruction, source restoration and canonical completeness are therefore unchanged. The first-root shear S=L is one explicit choice.

Degree and operation claims require their separate exact circuit certificates. No mere degree bound or presumed cancellation is used. The semantic checker authenticates the copied proof dependencies, verifies that all six live coefficient payloads agree with both centered sources, checks exact source-restoration cuts, and proves the displayed root-bound polynomials positive by nonnegative coefficients after x→x+64,m→m+16,Cabs→Cabs+16. These checks complement, rather than replace, the unbounded proof and inherited calibration.
