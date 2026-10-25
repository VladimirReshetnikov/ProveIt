# Q-cube normalization of the doubled product-square equation

This is an ordinary, code-free proposal over the same complete directly indexed BFS943 coefficient tuple as Staged84/85. It combines the previously proved q-cube coordinate normalization with the new doubled product-square kernel. No evaluator, emitted equation, checker, compiler, optimizer, PDF or new finite receipt is supplied or executed here. The manual schedules predict 81 operations at degree 750 and 82 at degree 560; they are not accepted circuit censuses or frontier endpoints. The balanced Staged85/328 point remains a different tradeoff.

The new statements below are the universal clearing identity, direct positive-input soundness after the shear, complete positive converse, and global leading forms. All later native/refutation conclusions are relative to the unchanged whole indexed source calibration and the identified ordinary Pell/rank/projection contracts. No new consistency proof, end-to-end formalization or global optimality claim is made.

## 1. Fixed instance and complete polynomial

The ten independent inputs are

    J,F,alpha,i,T,w,s,n,eta,zeta in Z_{>0}.

The four fixed ports beta,K0,MC,MF are exactly the complete indexed BFS943 tuple: Start0/Forbidden1, corrected initializer4, and MF_source shifted once. They obey beta>=31 odd, K0>0 and 0<MC<beta<MF<2beta. Their complete raw-byte SHA256 values are:

| Port | SHA256 |
| --- | --- |
| beta | `0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d` |
| K0 | `0a86821a704294199c2e1a50379d242c96840a3366e9d965689ba3d74605203f` |
| MC | `6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4` |
| MF_source | `48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737` |

This binds the whole coherent tuple, including the indexed native/controller theorem. It does not substitute K alone into a differently calibrated polynomial. Source hashes and the canonical-family contracts are pinned in SOURCE_PINS.json.

Define the following integer-polynomial abbreviations; none is another unknown:

    q=beta J+1, h=q-1, C=q-F-alpha, X=wq,
    mu=q^2+1, Y=q^3 s, k=eta+zeta, c=kY+eta,
    A=mu Y(X+1)+1, Delta=A^2-1, H=4A-5,
    V0=X mu^2 Y^2, E=1+V0(V0+1)k^2,
    R=[h(q-F)+alpha](q^2-1)+(MC+q MF)J,
    e=k-R-1, B=(K0+w)C-F,
    U=i c^2, a=Delta U^2 E, F0=1+a, G=E F0,
    Fsq=1+4aF0, Q=Delta(Fsq-1),
    b=c(T+alpha)-R, V=Fsq b-c,
    Kpos=X(3c-2X)+2.

Choose either L=V^2 or L=bV. The new complete carrier and equation are

    M=h mu^2 H,
    Z=h mu^2[H(n-LB)+Kpos]-H[mu^2 B+h e],
    RG=M^2 G,
    N=Q(Z^2-RG V^2)+(RG-Z^2)=0.                 (1)

All operations in (1) are ordinary polynomial arithmetic with fixed nonnegative powers. For proof notation set delta=Q-1, Dy=QV^2-1, kappa=Kpos/H, rho=e/mu^2, t=B/h and W=1+hL. Then

    N=delta Z^2-M^2 G Dy,
    Z/M=n+kappa-Wt-rho.                         (2)

The carrier identity is rational and unconditional; no divisibility, decoded sign or Pell meaning is presumed.

## 2. Universal old/new clearing identity

Take the Staged84 or Staged85 formula with the same weight policy and substitute

    Y_old=q^3 s, n_old=n-s,

leaving every other input, fixed port and kernel abbreviation unchanged. Its P_old=q^3 h. Direct expansion of its carrier gives

    Z_old=q^3 Z, M_old=q^3 M,
    N_old=q^6 N.                               (3)

In detail, the old hY_old term supplies q^3 h s, which cancels the -s in n_old. The remaining old low carrier is -q^3[mu^2 B+h e]. Both terms of the finalizer are homogeneous of degree two in Z,M. Thus its factor is q^6, not the q^12 factor of the older two-root norm.

Identity (3) is over the entire free-port polynomial ring and fixes the whole indexed tuple. It alone is not a positive-domain equivalence, since n-s may be nonpositive. Soundness is therefore proved directly below rather than applying a theorem requiring n_old>0.

## 3. Root recovery before transport

Y=q^3s is positive. All early Staged kernel hypotheses hold independently of n_old and B: E>1, F0>1, Fsq>c+1, Q>1, delta>0, H>0 and M>0. For any integral b, V=-c if b=0; otherwise |V|>=Fsq-c>1. Hence Dy>0. The identities

    Fsq=(1+2a)^2,
    Q=4 Delta^2 U^2 G

make delta and Dy both -1 modulo G. At a zero, delta*(Z/M)^2=G*Dy and prime valuations show G=g^2 for an integer g>0, with no coprimality assumption on M. Since F0=1 modulo E, its positive factors are coprime, so

    E=tau^2, F0=f0^2, g=tau f0.

The rational adjacent-Pell descent of Staged section3 applies to y=|Z/M|/g and yields an integer y>0 with

    QV^2-(Q-1)y^2=1, Z/M=epsilon g y,
    epsilon in {-1,1}.                         (4)

The proof-defined strong pair f=1+2a, I=2Ug satisfies f^2=Fsq, f^2-Delta I^2=1, Q=(Delta I)^2 and c^2|I. The same all-index folding theorem gives c=psi_A(p) at an odd p>=1. The first norm E=tau^2 excludes its first index: it would give k=2 and c=2Y+1 strictly between psi_A(1)=1 and psi_A(2)=2A. Therefore the unchanged bounds give

    k>=8V0+4, c>kY>=k>8q^5, c>X, Kpos>0.

The unconditional mask bound R<q^4+(alpha+2)q^2 implies b>c, and hence V>0, before the sign of B. Also

    b-e=c(T+alpha)-k+1>0, rho<b/mu^2.           (5)

No nonnegative e, positive shifted n_old, main rank p=R or decoded native condition has been used.

## 4. Direct positive-n sign bootstrap

For L=V^2, the positive identity

    a^2-g^2=E[(Delta U^2)E(Delta U^2-1)-1]>0

gives g<a. Since b>c>=3 and Fsq-1=4aF0>a, one has V>(Fsq-1)b>3g. Equation (4) gives y<3V/2, so gy<L/2.

For L=bV, c>=3 excludes p=1, so c>=psi_A(3)=4Delta+3 and V>4Q. Put S=Delta I, so Q=S^2>=4. Positive Pell classification of (4) gives SV=chi_S(j) for a positive odd j. The possibilities j=1 and j=3 give V=1 and V=4Q-3 and are excluded. Thus

    V>=16Q^2-20Q+5>8Q^2,
    b=(V+c)/Fsq>4Delta^2(Fsq-1)
      =4Delta^3 I^2>4g.

Again y<3V/2 gives gy<3bV/8<L/2. This fifth-index argument precedes transport and does not require the canonical R>3q bound.

For either weight suppose B<=-1. Since W=1+hL and h>0, Wt<-L. Solving (2) with (4), using kappa>0 and (5), gives

    n=epsilon gy-kappa+Wt+rho
      <L/2-L+b/mu^2<0.

The last inequality follows from V>1, mu^2>2 and either L=V^2 with b<V, or L=bV. It contradicts the actual positive input n. Therefore B>=0, and B=(K0+w)C-F with F>0 forces C>0. The old negative term -Y/q^3 is absent from this proof; it was not needed for the strict contradiction. No positivity of n-s has been asserted.

## 5. Later arithmetic and the original native interface

Now C>0 supplies 3q<R<q^4-2. The retained normalized rank and signed-index contracts use the same strong pair, c^2|I, c>2R, c>2p and fixed-minus residues. They give p=R; odd rank then yields q even and J odd. These results do not require n_old>0.

The carrier z=Z/M=epsilon gy is integral. The coprimality gcd(mu^2,hH)=1 is now available, and clearing (2) modulo mu^2 gives mu^2|e. The unchanged first-index congruence gives n0=(R+1)/2, and the same ratio bounds supply the strict whole-product height estimate. In these steps n is used only as an integer carrier addend.

Adding the integer rho to (2) and clearing modulo H gives H|h Kpos. This implies the weaker inherited premise H|q^3 h Kpos. Cancel only2 through odd H and apply the accepted ENTIRE-product projection and height bound to infer X=2^R; no arbitrary unit is cancelled through a composite H. Hence kappa is integral. Equation (2) now makes WB/h integral, and W=1 modulo h gives h|B. Thus t is a nonnegative integer. The old q^3|Y premise holds literally by construction.

All fixed-minus parity, exact half-binomial rounding and fresh UNscaled source reconstruction at Y(X+1)+2 therefore have their original hypotheses. The whole indexed943 native/controller calibration supplies a finite syntactic ZFC refutation. This proves soundness for positive new inputs even if n_old=n-s<=0. It does not claim a pointwise positive old zero on that sheared tuple; a positive old witness can instead be rebuilt canonically after decoding the refutation.

## 6. Complete positive converse with the corrected canonical premise

A finite refutation supplies the same complete indexed canonical outer/first/main family as the retained positive theorem, in particular

    Y>0, q^3|Y, E=tau^2, c=psi_A(R),
    R>3q, R=3 modulo4,
    integer t,rho>=0, s=Y/q^3>0, kappa>0.

The cubic divisibility is an actual canonical source promise, already used in the sealed q-cube proof section5 and the saturated canonical converse. It is not inferred merely from cofinality or imposed on every arbitrary predecessor solution.

Choose a fresh determinant-one Pell period modulo c^2*tau, giving a seed pair (f0,I0) with c^2*tau|I0 and i=I0/(c^2*tau)>0. Then U=I0/tau, a=Delta I0^2, F0=f0^2 and G=(tau f0)^2. Doubling this pair gives exactly f=1+2a and I=2f0I0=2Ug. Its even strong index is permitted by the retained auxiliary-completeness theorem; no odd I/c^2 condition is used.

Retain R>3q, not merely R>=3, for the shifted positive T. The auxiliary construction has V*=chi_S(R)/S, y=psi_S(R), S=Delta I and

    T*=(V*+c+R f^2)/(c f^2).

For v=(R-1)/2>=2, its inherited growth estimate gives V*>=9Q^2=9S^4. Since c<S, f^2<Q=S^2 and alpha<q<S, it follows that T*>V*/S^3>=9S>alpha. Thus T=T*-alpha is a positive integer. The weaker generic R=3 case would instead give T*=1 and would not prove this; that false generic positivity claim is not used.

The canonical seed estimates give f0>(A-1)I0>Xc>kappa and tau>Y>=s. Hence g=tau f0>kappa+s. With either chosen L, the old Staged positive converse supplies

    n_old=gy+(1+hL)t+rho-kappa-s>0.

Set the new s=Y/q^3 and n=n_old+s>0, keeping all other newly constructed inputs. Identity (3) gives q^6 N=N_old=0, hence N=0 since q>0. Equivalently n=gy+(1+hL)t+rho-kappa is directly positive. The seed, doubled strong pair, auxiliary pair and positive coordinates are all constructed afresh in this one coherent canonical family.

This proves both existential directions over ten strictly positive integers. It retains the same ordinary no-positive-zero/Con(ZFC) equivalence relative to the complete calibrated source theorem, without asserting either side separately.

## 7. Manual evaluation schedule and cost

Start from the actual Staged84 or Staged85 topological source. Move its already present q2/q3 gates before the new Y definition; this is a reordering only. Rename the old free input Y to s and add the one product Y=q3*s. The only gate deletions and carrier replacements are:

| Old gate | New treatment |
| --- | --- |
| `P1=q3*bJ` | delete; use `bJ=h` |
| `qm1Y=bJ*Y` | delete |
| `q3Bt=q3*Bt` | delete |
| `inner=qm1Y-q3Bt` | delete |
| `P1mu2=P1*mu2` | replace by `bJ*mu2` |
| `mu2inner=mu2*inner` | replace by `mu2*Bt` |
| `P1e=P1*e` | replace by `bJ*e` |
| `brk=mu2inner-P1e` | replace subtraction by addition |
| `Znum=Zpart1+Zpart2` | replace addition by subtraction |

All other gate expressions, after using the new Y abbreviation, stay the same. The two sign-operation replacements exchange one sum and one difference. Three products and one difference are deleted, while one product is added. The manually proposed breakdowns are consequently

    V^2: (50,19,15) -> (48,19,14), total81,
    bV:  (51,19,15) -> (49,19,14), total82,

in product/sum/difference order. All fixed-scalar products count. q3 remains live through Y. This is a complete local schedule derivation, not an independently materialized liveness/census certificate. Any later executable packet must bind every actual row, all ten free inputs and all four ports, and reject meaningful mutations.

## 8. Global degrees and complete leading forms

The q-cube substitution changes which term leads b. Write q0=beta J, k0=eta+zeta and T0=T+alpha. The actual leading forms are

    Y0=q0^3 s, c0=k0 q0^3 s,
    A0=q0^6 w s, U0=i k0^2 q0^6 s^2,
    E0=q0^22 w^2 s^4 k0^2,
    a0=i^2 q0^46 w^4 s^10 k0^6,
    G0=i^2 q0^68 w^6 s^14 k0^8,
    Fsq0=4i^4 q0^92 w^8 s^20 k0^12,
    Q0=4i^4 q0^104 w^10 s^22 k0^12,
    b0=k0 q0^3 s T0,
    Vaux0=4i^4 q0^95 w^8 s^21 k0^13 T0,
    M0=4q0^11 w s, B0=w(q0-F-alpha).

In particular deg(c(T+alpha))=6 exceeds deg(R)=4. Substituting into only the old degree436/328 homogeneous forms would miss this change and give the wrong result.

The degrees of (A,U,E,a,G,Fsq,Q,b,V,M,B) are (8,11,30,68,98,136,152,6,142,13,2). Thus L=V^2 has degree284 and Z degree299; L=bV has degree148 and Z degree163. The two final summands delta Z^2 and M^2 G Dy have bounds

    L=V^2: 750 and560,
    L=bV:  478 and560.

For V^2 the unique dominant summand has complete leading form

    2^14 i^20 q0^506 w^46 s^108 k0^64
      (T+alpha)^4 (q0-F-alpha)^2.              (4)

Its coefficient at J^506 w^46 s^108 i^20 eta^64 T^4 F^2 is 2^14 beta^506>0; the exponents sum to750. For bV the unique dominant summand is the negative right-hand product, with complete leading form

    -2^10 i^14 q0^384 w^34 s^80 k0^46
      (T+alpha)^2.                            (5)

Its coefficient at J^384 w^34 s^80 i^14 eta^46 T^2 is -2^10 beta^384, nonzero; the exponents sum to560. These are global algebraic degree arguments for (1), not evaluations along a ray or only on its zero set. The provisional literal implementation still needs an independent full-interface/degree audit before any numerical endpoint is accepted.

## 9. Boundary and prior work

The q-cube substitution, integral shear and reduced clearing were already established for the older two-root equation by `ten-positive-qcube-normalization`, whose proof credits the earlier concurrent gap-fusion substitution. The present new combination is its application to the Pell-doubled product-square equation, with the degree-two q^6 scale factor and the direct sign/completeness argument above. Product-square extraction and Pell doubling are likewise inherited, not newly claimed here.

No frozen source, coefficient, page, review, common report or Lean file is changed. No finalizer or bootstrap improvement beyond this concrete coordinate tradeoff is claimed. A future finite packet requires a complete literal builder/checker and source bindings, all global coefficients/interfaces and witnesses, normal/optimized checks and byte-exact rebuilds, after separate review and release. This proposal itself adds no executable package and requests no canonical promotion.
