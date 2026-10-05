# BB core (3,7,0): exact Rayleigh endpoint certificate

Complete proof, 1 October 2026. All five exact coefficient reconstructions
and the separate matrix reconstruction have passed. All five coefficient
hashes match a separate Horner/tensor-Bernstein implementation. The result
has not been externally refereed or formally verified.

## Aggregate support formulas

The first two A rows have neighborhood {B0,B1}; the third has neighborhood
{B1}. Remove mask-4 exterior-left rows temporarily. Let m count the remaining
L rows, u those meeting B0, z those meeting B2, and v those meeting both B0
and B2. Let p count L pairs matching B0,B1, q count L bases, h count pairs
completed by a generic mask-3 row, and g count pairs matching B0,B2.

Set d(S)=|S|, H3(S)=h(3,S), H7(S)=h(7,S), and

    G(S)=1{A1 in S}+1{A2 in S}
         -1{{A1,A3} subset S}-1{{A2,A3} subset S}.

Direct endpoint-set counting gives

    E=p+2m+u+3,                  x=q+2h+g+3z,
    r_S=p*d(S)+u*H7(S)+(m-u)*H3(S)+1,
    v_S=q*d(S)+h*H3(S)+g*G(S)+z,
    b_ST=p*h(S,T)+u*chi(7,S,T)+(m-u)*chi(3,S,T).

The constant terms apply to the seven nonempty R types. In v, the pair
{A1,A2} contributes h when S meets that pair. The pair {Ai,A3} contributes
h if A3 is available to R, and otherwise g if Ai is available. This gives
the displayed H3 and G combination without allocation multiplicities.

All remaining L rows meet B0 or B1. Therefore

    h=mz-z(z+1)/2,          g=uz-v(v+1)/2,
    1<=p,  1<=u<=m,  m>=2,
    u(m-u)<=p<=u(m-u)+u(u-1)/2.

For the p bounds, let c count rows meeting both B0 and B1. Then
p=u(m-u)+uc-c(c+1)/2, where 0<=c<=u is an integer. The first two formulas
are elementary pair counts.

The rank-three augmented matroid with a generic mask-3 row V, private B1
row Y, and private B2 row Z has basis polynomial

    q+hV+gY+pZ+zVY+mVZ+uYZ+VYZ.

Applying Wagner's rank-three Rayleigh theorem to (V,Z) after deleting Y,
and to (Y,Z) after deleting V, gives

    q<=min(hp/m,gp/u).

The cited result is David G. Wagner, “Rank-three matroids are Rayleigh,”
Electronic Journal of Combinatorics 12 (2005), N8, Theorem 1.1:
https://www.maths.tcd.ie/EMIS/journals/EJC/Volume_12/PDF/v12i1n8.pdf

The augmented matroids have rank three even if deleting mask-4 rows lowers
the original L rank, because p>0 and the added private B2 row is present.

## Exact Schur reduction and concavity

On the seven R support classes put

    M=3rr^T/(4E)-b,       w=3xr/(4E)-v.

The earlier small-cover argument proves M is PSD for every actual integer
population with p>0. The data `cross.json` give an exact vector Y satisfying
MY=w, verified directly from fresh coordinate-injection counts. The symmetry
interchanging A1,A2 reduces this computation to the five class orbits
{1,2}, {3}, {4}, {5,6}, {7}; no unverified inverse is imported.

The remaining Schur scalar is

    S=3x^2/(4E)-w^T Y=N/(pD),

where the full exact expression is in `schur.txt`. It is quadratic in
q,h,g,z and D depends only on m,u,p. This formula can be verified by the
matrix identity and scalar subtraction, without trusting its derivation.
Each coordinate of the stored solution Y has denominator D or pD, so the
positive denominator checks below make Y defined at every actual population.
No invertibility of the full R block is needed: MY=w gives the exact
completion of the square

    alpha*b^2+2b*w^T R+R^T M R
      =(R+bY)^T M(R+bY)+b^2*(alpha-w^T Y).

Thus M PSD and S>=0 suffice, including any singular R block.

The coefficient of q^2 in N is nonpositive: its negative has 50
nonnegative monomials after m=u+B, u=1+U, p=1+P. The denominator D is
strictly positive on all integer parameter cases: substitute either
(u,m-u,p)=(2+U,B,1+P) or (1+U,1+B,1+P). Both resulting polynomials have
53 nonnegative monomials and positive constants 790 and 648 respectively.
These two cones cover 1<=u<=m, m>=2. Hence S is concave as a function of q.

If z=0 then q=h=g=0 and S=0. For z>0 it therefore suffices to prove
nonnegativity at q=0 and at the smaller Rayleigh upper endpoint.

## Exact nonnegative-parameter regions

Write the four intersection populations as

    v=|B0 intersect B2|,   w=|B2 outside B0|,
    x=|B0 outside B2|,    y=|neither|.

Thus u=v+x, z=v+w, m=u+w+y. The p interval is parameterized by

    p=u(m-u)+u(u-1)T/2,      0<=T<=1.

The proof checks the following five polynomial regions. All variables not
explicitly bounded by one are nonnegative.

1. q=0, v=0: put u=1+X, z=1+W, m=u+z+Y.
2. q=0, v>=1: put v=1+V and use the four-population formulas above.
3. Upper endpoint, v=0: it is q=hp/m, with the parameters in case 1.
4. Upper endpoint gp/u, v>=1: put

       R=v(v+1),
       Ystar=w*[u(2v+w+1)-v(v+1)]/R,
       y=Ystar+Y.

5. Upper endpoint hp/m, v>=1: put y=Ystar*C, where 0<=C<=1.

The numerator of Ystar is nonnegative, since u=v+x and

    u(2v+w+1)-v(v+1)=v(v+w)+x(2v+w+1).

Moreover

    uh-mg = [v(v+1)/2]*(y-Ystar).

Thus cases 4 and 5 are exactly the two choices of smaller Rayleigh bound.
When Ystar=0, case 5 simply means y=0, and the parameterization remains valid.
When v=0, uh-mg=-u*z(z+1)/2<0, which justifies case 3.

For the hp/m endpoint multiply N by m^2 after substitution; for gp/u multiply
it by u^2. These positive factors clear the q denominator. In cases 4 and 5,
substitute the rational expressions with denominator R and multiply by R^7
and R^9 respectively. These powers clear all remaining denominators and are
positive because v>=1.

## Bernstein coefficient criterion

Each resulting polynomial is expanded in ordinary monomials of its unbounded
nonnegative parameters and Bernstein polynomials of the bounded parameters T
and, in case 5, C. The conversion is exact: a polynomial sum_j a_j T^j of
degree d has Bernstein coefficients

    b_k=sum_(j<=k) a_j binom(k,j)/binom(d,j).

Every resulting rational coefficient must be nonnegative. This proves the
polynomial is nonnegative throughout its whole region, not merely at sampled
populations. The full checker also verifies the Schur identity, q-concavity,
the denominator cones, and every polynomial transformation.

All five checks pass. Their coefficient counts, including identically zero
slots retained by the conversion, are respectively 2,325; 11,644; 3,886;
93,092; and 254,167. Case 5 uses Bernstein degrees 5 in T and 9 in C; each
other case uses degree 5 in T only. The original final-region reconstruction
took about 699 seconds and found no negative coefficient.
In total 363,633 coefficients are strictly positive; every other retained
entry is zero. The independent implementation obtains the same five complete
coefficient hashes using weighted Horner composition and simultaneous
Bernstein conversion.

Thus concavity proves the base BB class matrix PSD. The previously proved
mask-4 monotonicity lemma restores all deleted private rows. For completeness,
adding t private rows leaves E,r,M fixed, changes x to x+tE and v to v+tr,
and hence changes w to w-tr/4. The earlier degree-five bound supplies
M>=rr^T/(12E). Writing M+ for its pseudoinverse, this implies r is in its
range and r^T M+ r<=12E. Base positivity gives w in the same range and
w^T M+ w<=3x^2/(4E). The new scalar remainder is

    S(t)=S(0)+[3x/2+(r^T M+ w)/2]t
                +[3E/4-(r^T M+ r)/16]t^2.

Cauchy--Schwarz gives |r^T M+ w|<=3x, so both added coefficients are
nonnegative. This restores all deleted private rows, even if M is singular.
The nonnegative finite-twin correction then gives every finite labeled R
Hessian in this core profile.

The replay commands are:

    python -O derive_scalar.py
    python -O check_support_counts.py
    python -O check_zero_overlap.py zero
    python -O check_regions.py zero
    python -O check_zero_overlap.py h
    python -O check_regions.py g
    python -O check_regions.py h

The first command reconstructs all matrix entries using explicit coordinate
injections and checks the stored exact Schur and cross-column identities.
The other commands reconstruct every rational coefficient, reject any
negative coefficient with an explicit exception, and record a canonical
SHA-256 coefficient stream. All tests remain active under Python -O.

This is one nested BB profile. It does not itself prove the full retained
quartic theorem or make a new scalar ULC claim.
