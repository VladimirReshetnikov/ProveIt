# Independent review of the degree-190 positive polynomial

## Scope and outcome

Reviewed `compact_work/positive190/PROOF.md`, the 120 literal graph rows,
the retained free-chart proof, and the retained whole-center algebra.
No mathematical discrepancy was found in the new combination. This is
an AI-assisted internal review, not outside peer review or a newly checked
Lean/Rocq theorem. The named native/refutation calibration and inherited
Pell folding/projection results remain explicit mathematical dependencies.

## New signed transport argument

The chart has A>q^2>=1024 and positive U,E. The norm is unchanged up to
the square scaling factor16, so its valuation proof still makes G square.
With g=sqrt(G)>0 the rational coordinate is y=abs(Z)/(4Mg), and the
adjacent-Pell descent is unchanged. The factor4 is already accounted for
in the equation z=epsilon*4*g*y.

The inherited free-chart proof deliberately allows the auxiliary index
three. Its strict estimate abs(b)>4*Delta*f-1 and integrality imply the
exact inequality abs(b)>=4*Delta*f. This step has no assumption on the
sign of R,B,C or b. In particular it does not incorrectly import the
stronger index-five estimate from the scaled chart.

The elementary inequality E<=U^2*E^2 gives

    g^2=E+Delta*(UE)^2 <= A^2*(UE)^2,

and hence g<=AUE. Together with y<3abs(V)/2, the center estimate
abs(Omega)<5AUE abs(V), and abs(V)<3f abs(b)/2, this gives

    4gy+abs(Omega) < (33/2) AUE f abs(b)
                  <= [33A/(8Delta)] b^2UE.

The advertised final bound below L/3 is valid already for integer A>=16,
because 8(A^2-1)-99A>0 at16 and is strictly increasing thereafter.
It therefore holds with substantial margin in the actual chart.

The inverse correction e*<=k-R-1<b is valid for every signed integer R:
k>=2 gives a nonnegative subtracted correction, and
b-(k-R-1)=cT-k+1>0. Thus rho<abs(b)/q^7<L/2, including the case of
negative b and negative rho. If B<=-1 then
(1+hL)B/h=B/h+LB<-L. Equation(1) consequently gives
n<L/3-L+L/2<0, which is impossible. There is no cancellation of possibly
negative quantities and no use of the later mask bound before C>0.

## Edge cases and denominator recovery

At every norm zero V is nonzero. The inherited argument excludes b=0 by
0<y^2-c^2<1; hence L=b^2UE is positive. The cases B=0 and T=1 are not
excluded: the proof needs only B>=0 after the contradiction argument.

Omega is an integer polynomial, so z integral implies z+Omega integral.
The old carrier authentication can therefore be applied to the uncentered
part. The only required property of its new transport coefficient is
W=1+hL=1 modulo h. Modulo H the changed term still vanishes because it
is multiplied by H. The unchanged cubic inverse identity supplies
q^4|e* before projection, with the explicit third-primary estimate; no
incorrect early cancellation of3 occurs. Only after X=2^R does q become
a power of two and the full q^7 denominator become available. Finally,
integer sigma-WB/h gives q^3|Y and h|B as in the parent.

The canonical completeness witnesses have b,V>0, and the whole-center
bound proves Omega>0. The parent estimate g>kappa+sigma+abs(rho), together
with y>=1 and t=B/h>=0, makes the new n strictly positive. All terms in
its definition are integers. Changing n alone does not alter any Pell
or native data used to construct the witnesses.

## Literal definitions and exact degree

Every new center row in the JSON graph agrees with the definitions. In
particular `V0k` is ell=v*k, `V0kk` is ell+k, `Dtau` is E, `qY` is ybar,
`cTR` is b, `UE` is U*E, and `Dg` is G. The polynomial carrier includes
both -LB and -Omega, and the final norm scales G by16 in both occurrences.

The independent standard-library script `check_center190.py` expands the
center from scratch in Z[A,ybar,k,U,b,c], verifies its exact formal-quotient
identity and recomputes all norm-defect coefficients. It confirms 84 center
terms, 594 defect terms, and degrees59 and94 at weights(4,2,1,5,4,2).
The full weighted top is

    8 A^6 ybar^8 k^8 U^6 b^2 (A^2-6 ybar^4).

For q0=beta*J and k0=eta+zeta, the actual leading substitutions are

    A0=q0^2*w*s,  ybar0=q0*s,  U0=i*k0^2*s^2,
    b0=-q0^3*(q0-F),
    Q0=4*q0^24*w^10*s^22*i^4*k0^12,
    M0=24*q0^10*w*s.

Multiplying Q0*M0^2 by the displayed defect top yields exactly

    9*2^11*q0^74*w^18*s^52*i^10*k0^32*(q0-F)^2*(w^2-6s^2).

Its degree is190. The remaining four pieces have degree at most184,154,
142 and70, so they cannot cancel it. Because beta is a fixed positive
integer, the displayed form is nonzero after q0=beta*J. This confirms the
exact degree for the actual fixed tuple; it is not merely a generic-port
bound or a ray experiment.

## Qualification

The argument proves the new bridge once composed with the specifically
identified inherited interfaces. It does not establish a globally simplest
equation, assert a solution or prove consistency, and it does not turn the
ten positive input variables into ten unrestricted integer variables.
