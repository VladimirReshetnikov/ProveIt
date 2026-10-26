# Admissible-denominator interpolation:77 operations,degree348

This is a small matched composition of two retained results,not an unqualified novelty or global-optimum claim: apply the Trace_Radical unsquared-trace theorem to the retained77-operation q4-denominator graph. The resulting point fills the operation/degree gap between76/352 and79/290 in the five-point incoming trace table. It is separate from the principal85/232 inverse-Lucas improvement.

## Entire polynomial

Use the same ten positive inputs and complete principal four-port tuple as ../PROOF.md. Define

    h=beta J,q=h+1,C=q-F-alpha,X=qw,Y=q³s,
    k=eta+zeta,c=kY+eta,A=Y(X+1)+1,Delta=A²-1,H=4A-5,
    ell=(XY)(kY),E=1+ell(ell+k),
    R=[h(q-F)+alpha](q²-1)+(MC+qMF)J,
    B=(K0+w)C-F,U=ic²,a=Delta U²E,F0=1+a,G=EF0,
    f=a+F0,Q=4Delta aF0,b=cT-R,V=fb-c,L=bV,
    K=X(3c-2X)+2,e=k-R-1,D=q⁴,M=hDH,
    Z=hD[H(n-LB)+K]-H[DB+he],
    P=Q(Z²-M²GV²)+(M²G-Z²).

There are no additional unknowns or division gates. The JSON specifies every binary gate. The proof-only variables are z=Z/M,kappa=K/H,rho=e/D,t=B/h,W=1+hL; the exact carrier identity is z=n+kappa-Wt-rho.

## Complete change to the inherited proof

The root extraction,trace-linear signed folding and auxiliary-index exclusions in ../inherited_trace/PROOF.md §§3–4 use only q|X,Y and Y>=q. They yield integral z=epsilon gy,positive L=bV,gy<L/2,|b|<L,and first/main indices k=2psi_(1+2XY²)(m),c=psi_A(p),with m>=2,c>8XY³ and K>0. Since e=k-R-1<b and D>2,the same signed carrier bootstrap gives B>=0,C>0. The calibrated bound3q<R<q⁴-2,trace residues modulof andc,and retained normalized-rank theorem then give p=R,R odd,q even.

Reducing Z modulo D yields D|hHe. Since q|Y,H=-1 moduloq and h=q-1,we have gcd(q,hH)=1,so q⁴|e. The first Pell congruence is k=2m modulo4XY²,whose modulus is divisible by q⁷ and therefore q⁴. The monotonicity argument gives m<R,and hence |2m-R-1|<R<q⁴. Thus2m=R+1. The full recurrence now gives4XY²|e. Because D=q⁴ divides4XY²,rho is an integer; it is nonnegative since psi_(1+2XY²)(m)>=m.

Clearing h in the carrier now yields H|hK. The same universal projector and whole-product estimate as ../PROOF.md §4 (with multiplierh rather than6h) give X=2^R and positive integral kappa. The remaining carrier gives h|B because W=1 moduloh. The scale q³|Y is already literal. This is exactly the retained native reconstruction endpoint and gives a finite syntactic ZFC refutation.

Conversely choose the inherited canonical outer data with q³|Y and set s=Y/q³>0. The exact ratio theorem supplies positive eta,zeta. Choose the positive strong period seed and trace-linear positive T as in ../PROOF.md §5. Since D|4XY²,the authenticated first index gives nonnegative integral rho. Projection gives positive integral kappa and the standard seed bound gives g>kappa. Set n=gy+(1+hL)t+rho-kappa. This is strictly positive integral,and gives the required carrier z=gy. Thus P=0. The four fixed integers are not replaced by arbitrary interval-box parameters in the concluding native/refutation theorem.

## Exact cost and leading component

The source parent is ../inherited_trace/inherited/cofinal/provenance/centered/equation_q4_bV.json at77 operations and degree460. Replace its Fsqr row by trace_f=a+F0 and its sole use in V; no gate is added or removed. The full free-port graph relation is checked independently.

The degree of M is11 instead of13 for the XY-denominator trace76 graph,while the norm data stay unchanged. The unique dominant term -QM²GV² has degree348; the carrier-square term is lower. For q0=beta J,k0=eta+zeta,the complete highest homogeneous part is

    [P]_348=-2^8 q0^216 w^26 s^60 i^10 k0^34 T².

It is nonzero for beta>0 and has35 terms. The independent checker covers all77 gates through33 exact cuts,checks liveness,all coefficient bytes and the parent relation,reconstructs the entire leading form,and rejects both alternative operators at every gate:154 mutations. Normal and optimized receipts are byte-identical. No finite test is offered as the unbounded Pell proof.
