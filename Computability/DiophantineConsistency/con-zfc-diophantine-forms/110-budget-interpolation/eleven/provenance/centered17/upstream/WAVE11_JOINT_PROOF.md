# Joint determinant/common-sign compression

## Result and inherited boundary

The explicit packets give the unrestricted-integer variable/degree pairs **25/8, 23/12, 22/16, 21/20, 20/32, and 19/88**. They also retain the 24/12 parent of the projection family and an alternative 23/12 coordinate choice. Each polynomial is the sum of the squares of the residuals listed in its packet. No named polynomial register adds a variable, and all six coefficient ports are fixed integer numerals. Sections 1–4 prove the 25/8 and 24/12 constructions; Sections 6–8 prove the remaining exact polynomial projections.

Every packet has an integer zero if and only if the pinned wave-eleven `determinant26_octic.json` has an integer zero. This is a pointwise existential extension/projection equivalence in the retained arithmetic coordinates, not merely an appeal to cofinal canonical witnesses. Consequently, relative to that parent's stated native compiler, Pell, and refutation-calibration theorems, ZFC proves that the absence of an integer zero is equivalent to Con(ZFC). The new argument neither assumes nor proves consistency. It supplies no new kernel-checked Lean/Rocq theorem or encoded object-ZFC derivation.

The joint-positivity lemma is the exact elementary technique of source 68, `ConZFC_Joint_Positivity_Free_Lucas_2026-10-23`, `integer_system/PAIR_GUARD_PROOF.md`, Sections 1–2. The contribution here is its composition with the wave-eleven determinant/residue construction, and the selective retention of one eliminated coordinate to keep the resulting degree at eight. There is no global minimality or external novelty claim.

## 1. Universal two-sign lemma

For arbitrary integers x, y, t define

    G(x,y,t) = x*y - (t*t-x-y+1)^2.

Then x>0 and y>0 if and only if G(x,y,t)>0 for some integer t.

For soundness, G>0 implies xy>0, so x,y have the same nonzero sign. If x=-a and y=-b with positive integers a,b, then

    (t*t-x-y+1)^2 = (t*t+a+b+1)^2 >= (a+b+1)^2 > a*b,

contradiction. Thus both are positive. This argument permits every sign and every size of t, x, and y, and includes zero inputs without a hidden exception.

For completeness, set N=x+y-1>=1. Then xy-N=(x-1)(y-1)>=0. Let m=floor(sqrt(N)). Choose t=m if N-m*m<=m, and choose t=m+1 otherwise. In either case |t*t-N|<=m. When N is a square the error is zero. When N is not a square, m*m<N, so (t*t-N)^2<N<=xy. Thus G>0. Floor and square root occur only in this mathematical witness-selection recipe, never in a defining polynomial.

For integers p,q,r define Pos(p,q,r)=1+p*p+q*q+r*(r+1). Its value is always positive because r*(r+1)>=0 on the integers. Every positive integer n is a value: 4n-3 is positive, is 1 or 5 modulo 8, and therefore is a sum of three squares by Legendre's three-square theorem. Modulo 4, exactly one of the three squares is odd. Write it as (2r+1)^2 and the other two as (2p)^2,(2q)^2, and divide the identity by 4. Therefore

    x>0 and y>0
      iff there exist integers t,p,q,r with
      x*y-(t*t-x-y+1)^2-Pos(p,q,r)=0.             (J)

This uses four private integer coordinates instead of six.

## 2. Exact parent interface

The copied parent is `upstream/determinant26_octic.json`, authenticated by `SOURCE_PIN.json`. Its first eleven rows are retained literally and in the same order. Its last two rows are exactly

    eta*zeta0 = Pos(eta_zeta_pos1,eta_zeta_pos2,eta_zeta_pos3),
    d = Pos(cone1,cone2,cone3),

where

    q = beta*(3*J3+1)+1,
    C = q-F-alpha,
    U = cone_A*F,
    W = cone_B*C,
    d = U*W-(q-U-W)^2,
    zeta0 = 1-V+j*c+h*E-eta.

The authentic fixed numerals are beta,K0,MC,MF of the entire source34 `mixed-parity-unrounded-1064921` tuple, together with cone_A=2^1113 and cone_B=2^666104. MF is already shifted by beta and is not shifted again. `../guards/COEFFICIENT_BINDING.json` and its gzip payloads bind all six leaves; the parent component reconstructs and authenticates them. Neither the compiler tuple nor its determinant scales is changed here. Coefficient paths in the new packets are relative to the `joint` directory.

The parent's determinant has a universal signed soundness proof, and its completeness proof regenerates canonical compiler witnesses to establish d>0. The residue orientation also has its own canonical completeness proof. Those distinctions remain important upstream. Our new step applies to every zero of the resulting parent, hence does not need any further canonical restriction. In particular, all canonical parent witnesses lift through the recipe in Section 1.

## 3. Twenty-four variables, degree twelve

Delete the parent's six private guard coordinates and last two rows. Add t=pair_root and p,q,r=pair_pos1,pair_pos2,pair_pos3. Retain the first eleven rows and append

    d*(eta*zeta0)
      - (pair_root^2-d-eta*zeta0+1)^2
      - Pos(pair_pos1,pair_pos2,pair_pos3) = 0.     (D12)

There are 26-6+4=24 variables and 13-2+1=12 rows. The twenty retained arithmetic coordinates are

    J3,F,alpha,z,f,h,r,v_scale,w3,tau,
    eta,y,gamma,o,j,E,c,a,V,I.

The reused letter r in that coordinate list is the parent's strong-Pell parameter; the private Pos coordinate is named `pair_pos3` in every packet, so the variables are distinct. Likewise the polynomial q is only an abbreviation and is not a new unknown.

At any new zero the final row and (J) give d>0 and eta*zeta0>0. The universal Pos representation restores both deleted triples; every other parent row was unchanged. Conversely, every parent zero has these two strict inequalities, and (J) supplies the four new coordinates. All twenty arithmetic coordinates are kept fixed in both directions.

The determinant d has degree two and eta*zeta0 has degree three. The new row has degree at most six, and the old rows have degree at most four. Its degree-six homogeneous part is exactly

    -eta^2*(h*E+j*c)^2.

Thus the coefficient of eta^2*h^2*E^2 in the new row is -1. In the squared residual the coefficient of eta^4*h^4*E^4 is +1: among degree-six terms, only that term has zero c and j exponents and can contribute. Every other squared row has degree at most eight. The one polynomial therefore has exact degree twelve with coefficient +1 at eta^4*h^4*E^4, independent of all coefficient ports.

## 4. Twenty-five variables, degree eight

Instead retain a separate integer coordinate zeta with the additional quadratic row

    zeta - 1 + V - j*c - h*E + eta = 0.             (R)

Use precisely the eleven unchanged parent arithmetic rows, this restoring row, and the joint row

    d*(eta*zeta)
      - (pair_root^2-d-eta*zeta+1)^2
      - Pos(pair_pos1,pair_pos2,pair_pos3) = 0.     (D8)

The retained source rows continue to use their original eliminated expression zeta0. This is intentional: (R) forces zeta=zeta0, and hence there is no inconsistent hidden substitution. The coordinate list is the preceding twenty arithmetic coordinates, then zeta and the four private pair coordinates. There are 26+1-6+4=25 variables and 13+1-2+1=13 rows.

Both d and eta*zeta are quadratic, so (D8) has degree four. All other rows have degree at most four. The coefficient of pair_root^4 in (D8) is -1, and no other row mentions pair_root. Its square has coefficient +1 at pair_root^8. Thus the sum of squares has exact degree eight on the actual fixed coefficient slice.

Given a parent zero, set zeta=zeta0 and use (J). Given a new zero, (R) and (J) restore both original positivity triples. This proves the same existential equivalence as Section 3. Eliminating zeta by (R) gives exactly the Section 3 packet, an integer-polynomial projection. The one-coordinate/degree tradeoff is explicit rather than silently treating the cubic eta*zeta0 as quadratic.

## 5. Verification and comparison

`build.py` uses a restricted arithmetic AST parser for the inert source JSON, checks both source guard identities, emits fully expanded residuals, checks liveness and counts, expands the complete sums of squares over symbolic fixed ports, and checks the exact-degree coefficients. `check.py` is a separate standard-library sparse-polynomial verifier. It does not import the builder or SymPy, and independently checks the source pin, all residual identities, counts, degrees, selected coefficients, declaration closure, and the projection from 25 to 24 variables. It authenticates the actual fixed coefficient bytes against the parent binding. Normal and optimized runs are supported; acceptance checks do not use removable assertions.

Finite signed-box and constructive nearest-square tests are supplementary diagnostics, not substitutes for the universal proof in Section 1 or for the inherited native and Pell theorems.

The inspected baseline's determinant/residue octic has 26 variables. The new 25-variable octic saves one at the same degree; the 24-variable degree-twelve equation trades degree for another variable. The source68 nested positivity construction had 26 variables and degree sixteen; 24/12 is lower in both of those metrics, on the same unrestricted-integer domain. No claim is made that these dominate high-degree nine-positive or ten-integer constructions, or that fewer variables implies fewer operations, smaller coefficients, or a shorter fully expanded numerical polynomial.

## 6. Exact monic projections and the auxiliary row identity

For the following projections use the compact source system in `COMPACT_BASE24.json`, checked to equal every residual of `joint24_degree12.json`. In addition to the earlier abbreviations, put

    W=4*(3*w3+1), X=q*W, Y=(2*v_scale+1)*q^3,
    k=1-V+j*c+h*E, Delta=a^2+4*a+3.

Relevant source rows are

    a-E-Y=0, E-X*(a-E)=0, c-eta-k*(a-E)=0,
    V+c-f*o=0, I-(2*r+1)*c^2=0,
    S=I^2-Delta*(f^2-1)=0,
    A=I^2*(V^2-y^2)+y^2-1=0.

The sum of squares is zero over the integers exactly when all rows are zero. The identity

    A - Ared = (V^2-y^2)*S,
    Ared=Delta*(f^2-1)*(V^2-y^2)+y^2-1

therefore permits replacing A by Ared in either direction while retaining S. This is a zero-set-preserving row operation, not a claim that A and Ared are equal as free polynomials.

Every subsequent elimination has an integer-polynomial inverse. An equation z=P(other variables) can be deleted after substituting P for z everywhere else. Projection of any old zero gives a new zero; restoring z=P gives an old zero. No division, divisibility assumption, sign restriction, or new canonical existence argument is involved.

For `joint23_degree12.json`, eliminate V using V=f*o-c and retain A. The auxiliary row then has degree six, as does the joint row, and all other rows have degree at most four except the degree-three I definition. There are 23 variables and 11 rows. The joint coefficient at eta^4*h^4*E^4 in the final sum of squares remains +1; no other row contributes to that monomial.

Alternatively, `joint23_degree12_eliminate_I.json` replaces A by Ared, eliminates I=(2*r+1)*c^2, and retains V. Its strong, reduced-auxiliary, and joint rows have degree six; all others have degree at most four. It has the same 23 variables/11 rows/degree twelve and the same +1 certificate. These are two different coordinate choices, not a claim of a bijection preserving all 23 coordinates.

For `joint22_degree16.json`, replace A by Ared and eliminate both V and I using the same maps. Its ten rows have maximum degree eight. The reduced auxiliary row has leading term a^2*f^4*o^2 with coefficient +1, and is the only row of degree eight. Hence the sum of squares has coefficient +1 at a^4*f^8*o^4 and exact degree sixteen.

## 7. Twenty-one, twenty, and nineteen integer variables

For `joint21_degree20.json`, return to the original auxiliary A and eliminate V,I,a by

    V=f*o-c, I=(2*r+1)*c^2, a=E+Y.

The first source row is the monic definition of a. There are twenty-one variables and nine rows. The ordinary main, strong, and auxiliary rows now have degree at most ten; all other rows have degree at most six. The strong row has top term -Y_top^2*f^2, where

    Y_top = 54*beta^3*J3^3*v_scale.

Its square gives the coefficient at f^4*v_scale^4*J3^12 equal to 2^4*3^12*beta^12>0. The main row contains no f, and the original auxiliary contains no J3, so neither can contribute to this selected monomial. This proves exact degree twenty. This choice is better than eliminating E or eta alone from the 22-variable system, which gives degree twenty-four; those dominated alternatives are not emitted in the final packet set.

For twenty variables, the better route is to retain eta and eliminate both E and a, as well as V,I. The first two source rows give successively a=E+Y and E=X*Y. Thus the simultaneous restoration is

    V=f*o-c, I=(2*r+1)*c^2, E=X*Y, a=(X+1)*Y.

In this endpoint retain the ORIGINAL auxiliary A before the I,V substitutions. This is important: Ared would unnecessarily raise its degree. The packet `joint20_degree32.json` is a direct monic projection of the 24-variable source and has eight residuals. E and a have degree six, k has degree seven, eta*(k-eta) has degree eight, and the joint row has degree sixteen. The first Pell and main/strong rows have degree at most fourteen; the original auxiliary has degree ten. Thus the sum of squares has degree at most thirty-two.

The degree-six top form of E is

    E_top = (36*beta*J3*w3)*(54*beta^3*J3^3*v_scale)
          = 1944*beta^4*J3^4*w3*v_scale.

The joint row's top form is -eta^2*h^2*E_top^2. Its square is the only contribution of degree thirty-two. Therefore

    [eta^4*h^4*w3^4*v_scale^4*J3^16] Q20
      = 2^12*3^20*beta^16 > 0.

This proves exact degree thirty-two on the authentic tuple. Choosing a different elimination order that removes eta first can give 20/48 or 20/72; those dominated alternatives are not promoted or emitted in the final packet set.

Finally eliminate eta using c-eta-k*(a-E)=0, which now reads eta=c-Y*k. This gives `joint19_degree88.json`, with nineteen variables and seven rows. The exact unknowns are

    J3,F,alpha,z,f,h,r,v_scale,w3,tau,y,gamma,o,j,c,
    pair_root,pair_pos1,pair_pos2,pair_pos3.

The top form of eta has degree eleven and is

    eta_top = -h*X_top*Y_top^2
            = -2^4*3^8*beta^7*h*J3^7*w3*v_scale^2.

Because eta has larger degree than k, eta*(k-eta) has top form -eta_top^2 and degree twenty-two. The joint row has top form -eta_top^4 and degree forty-four. Every other row has degree at most thirty-four. Thus the final degree is exactly eighty-eight and

    [h^8*w3^8*v_scale^16*J3^56] Q19
      = 2^32*3^64*beta^56 > 0.

The original auxiliary row is retained here too. All restoration formulas are ordinary polynomials in the declared surviving variables. In particular, the nineteen-variable result does not quantify over any hidden X,Y,E,a,V,I,eta or fixed-numeral coordinate.

## 8. Portable exact certificates for the projection family

`build_projections.py` emits the higher-degree residuals as completely inlined, factored polynomial expressions. Their JSON packets also include explanatory register definitions, literal coordinate lists, deleted-row indices, and fully inlined restoration maps. The explanatory registers introduce no new variables. Keeping polynomial expressions factored avoids wasting space on a massive expanded sum of squares; it does not introduce an exponentiation function or change the object from an ordinary integer polynomial.

`check_projections.py` uses only Python's standard library and imports neither builder nor SymPy. It independently checks the compact 24-variable system against its fully expanded packet, the auxiliary row-operation identity, every deleted defining row, every inlined surviving row, the restoration maps, and declaration closure. It propagates upper degree and exact homogeneous components at that upper degree, permitting cancellation in those components. For each emitted equation it checks a specific nonzero coefficient at the claimed top degree. It never infers exact degree from an uncancelled gate-degree bound alone. Normal and optimized runs both pass.

The finite projection checks add no new metatheoretic assumption. Their universal existence equivalence is the elementary row-operation and monic-restoration proof above; their link to finite ZFC refutability still passes through the explicit inherited parent theorem. The family is a bounded set of demonstrated variable/degree tradeoffs, not an exhaustive search or proof of an optimal frontier.
