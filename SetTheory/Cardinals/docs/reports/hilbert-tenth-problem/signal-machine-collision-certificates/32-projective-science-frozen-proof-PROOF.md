# Five signal realization of fixed center projective returns

4 October 2026. This is a new proof packet. It preserves the preceding packets and uses their proved fixed-scale planar compiler as a stated dependency. No author or upstream executable, physical trajectory simulator, or saved collision schedule was run. The newly authored `static_algebra.py` was displayed and inspected before execution; it checks exact polynomial identities and rational matrix fixtures only.

## 1 Results and scope

The section has stationary markers L=0, X=x, Y=y, R=D, with 0<x<y<D, and one messenger at L outgoing at speed +1. Thus there are exactly five live signals. Put

    ξ=x−D/3,   η=y−2D/3,   u=(ξ,η)ᵀ,   z=(D,u)ᵀ.

**Theorem 1.** For every rational s₀>0, rational row b∈Q^(1×2), and A∈GL₂(Q), there is an effectively constructible finite deterministic rational-speed, number-preserving signal machine and a fixed complete binary-collision word with literal section return

    z ↦ Nz,       N=[[s₀,b],[0,A]].

Its exact complete-word chamber is a finite intersection of strict rational homogeneous linear inequalities. On D=1 this is a bounded open rational polygon P with the centered origin strictly inside. The construction produces its inequalities by a finite explicit pullback procedure. All stationary marker labels and the outgoing messenger phase are restored, so the word can be repeated without an unrecorded reset.

The normalized map is

    f(w)=Aw/(s₀+bw),      w=u/D,

with positive denominator on P. These are exactly the rational projective planar transformations fixing this standard center with an invertible homogeneous representative of positive scale there. A common scalar multiple gives the same projective transformation but a different full homogeneous return; the theorem realizes the requested representative itself.

The singular case det A=0 is excluded by the preceding full-section invertibility theorem. A nonpositive s₀ cannot give this return on a chamber containing the standard center: that center would have nonpositive final D. The theorem makes no assertion about arbitrary GL₃(Q) maps not fixing this ray, arbitrary prescribed guard polygons, one unchanged machine for all parameters, polynomial compilation size, optimal counts, or continuation through an accumulation point.

**Theorem 2.** For every rational v>1, an explicit 44-event word on this same five-signal section has both Zeno and non-Zeno infinitely valid inputs. On the initial ordered section its infinite-validity set is exactly D≥3y/2. Equality gives Zeno runs; strict inequality gives non-Zeno runs. In positive initial gaps g=(x,y−x,D−y), the boundary is 2g₃=g₁+g₂. This demonstrates why one constant scale-factor clock criterion cannot be imported into the shape-dependent setting.

## 2 Dependencies and elementary conventions

The preserved dependency `dependencies/positive_planar_PROOF.md` proves the positive-determinant compiler. `dependencies/invertibility_GL2_PROOF.md` proves full-section invertibility, collision parity, a seven-event orientation-reversing primitive J, and the extension to all GL₂(Q).

We use their following verified interface. For any C∈GL₂(Q) and λ>0 rational there is a nonempty positive-duration complete word, denoted F(C,λ), whose return is

    λ diag(1,C),

with a finite exact homogeneous guard list, center-strict chamber, and literal phase closure. For det C>0 all its events involve the messenger. For det C<0 it is a positive compiler followed by one seven-event J block, containing one marker-only event. Fresh phase-label copies are required at concatenation interfaces.

The elementary anchor scaling used below is included here to fix its chronology. A target at distance q>0 from a stationary anchor is launched on the first outward messenger hit at speed

    h=(a−1)/(a+1),       a>0,

while the messenger reflects toward the anchor. After an anchor bounce the messenger restores the target at aq, reflects, and finally bounces at the anchor. The four principal relative times and positions are

    (q,q), (2q,0), (2q+aq,aq), (2q+2aq,0).

Its duration is 2(1+a)q. Each stationary inner spectator p is crossed at p, 2q−p, 2q+p, 2q+2aq−p. The exact guard is that q and aq remain between the same stationary nearest neighbors. Monotone target motion and |h|<1 prove sufficiency; reaching or passing a neighbor forces an extra or simultaneous contact and proves necessity. A nearest-target scale has four events; with one inner spectator it has eight. A zero target velocity at a=1 is allowed, since its messenger collision partner still has a distinct speed.

For a global homothety λ<1, scale X,Y,R in that order; for λ>1, scale R,Y,X. Their counts are 4,8,12, respectively, for 24 events. Appropriate endpoint ordering in these orders adds no guard beyond the ordered section. This operation multiplies all positions and centered coordinates by λ. Its duration at incoming marker positions x,y,D is 2(1+λ)(x+y+D).

## 3 The eight event outer marker operation

Fix rational v>0 and write

    h=(v−1)/(v+1),
    d=vD+(1−v)y=y+v(D−y),
    t*=(v+2)D−(v+1)y.

Start with the messenger at L outgoing right. Cross X and Y transparently. At R launch that marker with speed h and reflect the messenger left. Bounce at stationary Y. On the next outward contact restore R to speed zero and reflect the messenger left. Cross Y and X transparently, then bounce at L.

The complete event table is:

| Event | Time | Messenger position | Contact and action |
|---|---:|---:|---|
| 1 | x | x | Cross X |
| 2 | y | y | Cross Y |
| 3 | D | D | Launch R with speed h; reflect messenger |
| 4 | 2D−y | y | Bounce at Y |
| 5 | t* | d | Restore R; reflect messenger |
| 6 | t*+d−y | y | Cross Y |
| 7 | t*+d−x | x | Cross X |
| 8 | t*+d | 0 | Bounce at L and restore outgoing phase |

The eight flight durations, including the initial outgoing flight, are

    x, y−x, D−y, D−y, v(D−y), v(D−y), y−x, x.       (1)

All are strictly positive under exactly the initial condition 0<x<y<D. The restoration identity is

    d−D = h(t*−D).

At the Y bounce, the moving R/Y gap is 2v(D−y)/(v+1)>0. The moving marker is monotone from D to d, both strictly beyond y, so it cannot hit Y or any inner marker. The messenger has no unlisted spectator between Y and R. Before the initial Y crossing and after the final Y crossing, the crossings of X and L have all been listed. The relative messenger/target speed is nonzero and their prescribed departing directions separate immediately. Consequently no extra target contact, omitted crossing, or simultaneous remote collision is hidden in the table.

Conversely, the initial strict ordering is part of the required section. There is no further inequality to fail in (1); all positive ordered inputs realize this eight-event word. Its exact return and duration are

    (D,x,y) ↦ (d,x,y),
    T_outer=2[(1+v)D−vy]=2[D+v(D−y)].              (2)

The endpoint d remains outermost even for v<1. Transparent crossings of Y must not be confused with its middle bounce: they occur in different messenger phases. For v=1 the temporary R label has speed zero and the eight timed events are retained.

## 4 Recenter the two inner markers

Put s=(v+2)/3. After the outer operation, scale both x and y about L by s, keeping d fixed. For s<1 use X then Y; for s>1 use Y then X. For s=1 use X then Y and retain both identity scale words. There are always 4+8=12 events and two fresh temporary marker labels in this convention.

For contraction, scaling X first leaves sx<x<y<d. Scaling Y next has its endpoints above sx because sy>sx, and below d because sy≤y<d. For expansion, Y moves first and its only possible new obstruction is sy≥d. Under sy<d it stays between x and d. Then X has endpoints x and sx below sy, and above L. Thus the exact combined raw chamber is

    x>0,   y−x>0,   D−y>0,   d−sy>0,             (3)

where

    d−sy = vD+(1−4v)y/3.

The fourth row is redundant for v≤1 and essential for v>1. In the expansion case, if it fails, Y must reach or cross the stationary outer marker during its first scale. Equality gives a simultaneous contact at the proposed restored endpoint; strict failure gives a prior extra contact. This is a first-failure necessity argument and does not continue a trajectory through that wrong event.

Each scale begins and ends with the messenger at L pointing right. Scaling X has four events. Scaling Y has the eight-event grammar

    cross X, launch Y, cross X, bounce L,
    cross X, restore Y, cross X, bounce L,

where the stationary spectator X is at its then-current location. The principal scale times and the four spectator times in §2 prove all these crossings are strictly ordered. No zero-time phase transfer is used.

The 20-event raw word has return

    (D,x,y) ↦ (d,sx,sy)

and duration

    T_raw=2[(1+v)D−vy]+2(1+s)(x+y).               (4)

It has three temporary marker labels and four supplied exact guard rows. In centered coordinates its matrix is

    N_v = [[s,0,1−v],
           [0,s,(v−1)/3],
           [0,0,v]].                            (5)

At the standard center x=D/3,y=2D/3, d=sD and

    d−sy=(v+2)D/9=sD/3>0.

All internal scale endpoints are strictly ordered by the preceding contraction/expansion argument. Thus every rational v>0 gives a full-dimensional center-strict chamber. The determinant is vs²>0, consistent with the even event count.

## 5 Correct the shape action to obtain a scale shear

Let A_v be the lower-right block in (5):

    A_v=[[s,(v−1)/3],[0,v]],
    C_v=s A_v⁻¹=[[1,(1−v)/(3v)],[0,s/v]].

Its determinant s/v is positive. Follow the raw word with F(C_v,1/s), or equivalently the fixed-scale compiler F(C_v,1) and then a global scale 1/s. The complete homogeneous return is

    diag(1/s,A_v⁻¹) N_v
       = [[1,0,k],[0,1,0],[0,0,1]],
    k=3(1−v)/(v+2).                              (6)

Write this map as E_(0,k): it changes only D, by D↦D+kη. The exact chamber includes (3) and every row of F(C_v,1/s) pulled back by N_v. Since N_v sends the center to a positive multiple of the center, every such row remains strictly positive there. It is incorrect to keep only the raw endpoint guard after appending the compensation compiler; the latter's chronology guards are also required.

As v ranges over positive rationals, k ranges over rational values in (−3,3/2), with inverse

    v=(3−2k)/(3+k).                              (7)

For any rational k outside this interval, choose n=max(1,ceil |k|) and δ=k/n. Then |δ|≤1 lies strictly inside the allowed interval. Compile n copies of E_(0,δ). These maps add their coefficients, so their product is E_(0,k). Each factor fixes the center exactly; hence the finite intersection of all pulled-back exact chambers is still center-strict. There is no empty-domain obstruction caused by large k. A zero requested coefficient can be omitted when another nonempty macro supplies the required timed return.

## 6 Arbitrary scale rows and the main theorem

For a nonzero rational row r=(a,b), use the rational matrix

    B=[[b,−a],[a,b]],       det B=a²+b²>0.

Chronologically perform

    F(B,1), then E_(0,1), then F(B⁻¹,1).

Direct multiplication gives

    diag(1,B⁻¹) E_(0,1) diag(1,B)
      = E_r := [[1,r],[0,I₂]].                   (8)

Both conjugating compilers have positive determinant. This offers a particularly simple alternative to coefficient subdivision: arbitrary rational rows use one fixed coefficient-one shear, at the cost of two parameter-dependent centered planar compilers. All three factors preserve the center ray with positive scale, so all pulled-back guard rows remain center-strict. For r=0 omit this shear prefix.

Now take the requested N=[[s₀,b],[0,A]]. First realize E_(b/s₀), then run F(A/s₀,s₀). Since

    [s₀ diag(1,A/s₀)] E_(b/s₀) = [[s₀,b],[0,A]],

the return is exactly N. The final compiler is available for either determinant sign; in the negative case it uses the seven-event J extension from the preceding packet. No new live signal is introduced.

### 6.1 Explicit guard production and exactness

Each elementary or compiled block has a finite list of strict homogeneous rational rows G_j z>0. Let M_j be its full return matrix. The exact guard list of a chronological composition of q blocks is

    G₁z>0,
    G₂M₁z>0,
    ...,
    G_q M_(q−1)...M₁z>0.                         (9)

The earlier compiler specifies its G_j effectively by the displayed endpoint lists for signed micro-shears and centered dilations. For the new raw block use exactly (3). Global homotheties require no additional row. This is a finite algorithm with rational arithmetic; no search over physical trajectories is needed.

Sufficiency of (9) follows inductively from the complete chronology of each block. For necessity, use the earliest block whose guard fails, after a valid prefix. That block's first-failure argument shows an extra collision, coincident contact, nonpositive prescribed flight, or wrong event order. Therefore the selected complete word fails. Prospective affine formulas are used only up to the first failure. The row list is exact, even if some rows are redundant.

All partial completed blocks send the center to positive multiples of itself. Each internal chamber is center-strict, so the intersection in (9) contains a neighborhood of the centered origin on D=1. Its first input rows imply 0<x<y<1, so the normalized chamber P is bounded. It is an open rational polygon; it is not being replaced by its closure or by a conveniently chosen smaller neighborhood.

Endpoint compatibility is necessary but weaker than (9). In centered variables the ordered cone is

    C={D>0, D/3+ξ>0, D/3+η−ξ>0, D/3−η>0}.

Any one-pass chamber must lie in C∩N⁻¹C. On normalized input w, write h=s₀+bw and q=Aw. The output endpoint inequalities are

    h>0, q₁+h/3>0, q₂−q₁+h/3>0, h/3−q₂>0.

They are strict affine rows and are strict at w=0. They do not replace the intermediate collision guards.

### 6.2 Phase and rule isolation

For every messenger-involving event give its incoming flight a fresh messenger label with the prescribed rational speed; use the successor phase after the collision. The final outgoing phase is identified with the whole macro's initial label. Fresh temporary marker labels distinguish every launch and restoration, including speed-zero identity scales. Stationary section labels are shared because they have the same physical roles.

The new raw and positive compiler events all involve the messenger. Their input sets are automatically distinct because the messenger phases are distinct. Their incoming and outgoing speeds are distinct since the messenger has speed ±1 and their moving target speeds lie in (−1,1).

The possible J suffix has its separately proved rational speeds and one marker-only collision. At that event the messenger label must remain unchanged; it cannot be advanced by a remote collision. A fresh copy of J's temporary fast-X label makes that marker-only input set unique. Fresh copies at interfaces prevent the standalone J entry label from accidentally sharing a rule with another block. J's own distinct-speed conditions were checked in the dependency.

Complete the finite rule table by the identity output for every other finite input set whose speeds are pairwise distinct. This is finite, deterministic, and number-preserving. It does not count an extra contact as part of the selected complete word. Every explicit event consumes and emits two signals; the completion preserves cardinality too. There remain exactly five live signals throughout every finite portion of the run. The argument concerns the specified fixed word, not global reversibility of the complete rule map.

## 7 Counts and a concrete coefficient one compiler

Let m(C,λ), t(C,λ), and g(C,λ) denote event, temporary-marker-label, and supplied-guard counts of the selected preceding compiler. These are explicit integers obtained from its rational factorization and subdivisions. For det C>0, let K be the sum of its signed shear subdivision counts, T its full-transfer count, B_num∈{3,4} its shear-block count, H its positive determinant subdivision count, and ε=1[λ≠1]. Then

    m(C,λ)=18K+3T+14H+24ε,
    t(C,λ)=4K+3H+3ε,
    g(C,λ)=4K+4B_num+8H.

For the raw word we retain the two identity scales at v=1, so its counts are always 20 events, 3 temporary labels, 4 supplied rows. The corrected shear in (6) therefore has

    20+m(C_v,1/s) events,
    3+t(C_v,1/s) temporary marker labels,
    4+g(C_v,1/s) supplied rows.

All these events involve the messenger, so fresh labeling uses exactly m+t+4 meta-signals. Counts include redundant guards and retained zero-parameter words; no minimization is asserted.

For the single coefficient-one kick, v=1/4, s=3/4, and

    C_v=[[1,1],[0,3]].

The positive compiler's determinant-one factor has chronological blocks y(−2), x(1/3), y(6), with subdivision counts 8,2,24. Thus K=34,T=4,B_num=3. The determinant dilation has H=8. The fixed-scale compensation has 736 events; global scale 4/3 adds 24. Including the raw 20 gives

    780 events, 166 temporary marker labels,
    216 supplied guard rows, 950 meta-signals.

For b≠0 in Theorem 1, put r=b/s₀ and B as in §6. One explicit total count is

    m(B,1)+780+m(B⁻¹,1)+m(A/s₀,s₀).

The guard and temporary-label counts add in the same way, with 216 and 166 for the middle kick. For b=0 only the final compiler is needed. If det A<0, the selected final compiler adds seven events, three temporary X labels, and one marker-only event beyond its positive component. In general, if r_J is the number of these marker-only J events, the fresh messenger label count can be m−r_J; the total is m−r_J+t+4. In this chosen construction r_J is at most one.

The determinant of the full return is s₀ det A. Every scale shear and positive centered compiler has even length; the negative-determinant case appends one odd J block. Thus sign(det N)=(−1)^m agrees with the previously proved collision parity theorem.

## 8 Exact repeated validity and the clock criterion

Let the full exact cone be Q={z:Gz>0}, with normalized polygon P. Literal phase closure gives

    infinitely valid complete word
      ⇔ G N^n z>0 for every n≥0.                 (10)

On D=1 the same set is

    K={w: f^n(w) is defined and belongs to P for every n≥0}.

The denominator is positive at each valid iterate. Equation (10) also expresses K as an intersection of countably many strict rational affine half-planes in initial w. It is convex and contains the center, but this packet does not classify its semialgebraicity. The preceding fixed-scale planar spectral classification cannot simply be applied to the nonlinear normalized map f.

Every event time and every block duration is a rational homogeneous linear form on its exact chamber. The whole macro duration is therefore ℓz for a rational row ℓ. For the particular compiler above there are constants c₁,c₂>0 with

    c₁D≤ℓz≤c₂D on Q.                            (11)

For a nonzero row the first block F(B,1) already takes at least 2D by the preceding compiler. For a zero row the final fixed-scale GL₂ compiler does so. Thus c₁=2 is available. For the upper bound, every intermediate time and position is a fixed linear form in the initial coordinates, and the closure of the normalized ordered input triangle is compact. There are finitely many such forms. Their absolute values have finite maxima there, giving a finite upper bound on duration and on all positions reached during a valid macro. No denominator involving input shape appears before normalization.

For an infinitely valid input put z_n=N^n z and D_n=(z_n)_0>0. Then

    Zeno ⇔ Σ_(n≥0)D_n<∞ ⇔ N^n z→0.              (12)

The first equivalence follows from (11). For the forward direction of the second, bounded normalized marker positions imply every coordinate of z_n is O(D_n), so summability forces z_n→0. Conversely, for a finite-dimensional constant matrix, convergence of N^n z to zero implies that every eigenvalue active in its cyclic subspace has modulus less than one; its terms then decay at a polynomial times geometric rate and are summable.

Equivalently, let V_z=span{z,Nz,N²z}; replace the three vectors by a basis if dependent. A valid orbit is Zeno exactly when every eigenvalue of N restricted to V_z has modulus below one. At the center this reduces to s₀<1. It does not generally reduce to that condition for all inputs.

If N and z are rational and the run is Zeno, V_z has a rational basis, I−N is invertible on it, and the accumulation time is rational:

    T_total = ℓ [(I−N)|_(V_z)]⁻¹ z.

Using the full inverse (I−N)⁻¹ without checking invertibility would be wrong: inactive unit eigenmodes may exist. During a Zeno run all five signals approach L, because their positions in macro n are bounded by a constant times D_n. No evolution beyond that accumulation point is asserted.

## 9 A 44 event word with two clock behaviors

Fix rational v>1, use the 20-event raw word of §§3–4, and append the 24-event global contraction 1/v. Put

    s=(v+2)/3,   r=s/v=(v+2)/(3v),   a=(v−1)/v.

Then 1/3<r<1, and the exact section return in physical coordinates is

    D'=D−ay,   x'=rx,   y'=ry.                   (13)

The global contraction introduces no further guard, so the exact one-word chamber remains (3). The fourth row is equivalent to D'>y'. The complete word has 44 messenger-involving events, 6 temporary marker labels, 4 supplied strict rows, and 54 meta-signals with fresh phases.

Its exact duration is

    T(z)=2[(1+v)D−vy]+2(1+s)(x+y)
          +2(1+1/v)[s(x+y)+vD+(1−v)y].           (14)

The three summands are the outer operation, the two inner scales, and the three global scales. In particular T(z)>2D. It is bounded above by a constant times D on (3), for example

    T(z) < [2(1+v)+4(1+s)
              +2(1+1/v)(2s+v)]D.

Define c=D−3y/2. Since 1−r=2a/3, c is invariant under (13). Algebraic powers give

    x_n=r^n x,
    y_n=r^n y,
    D_n=c+(3y/2)r^n.                            (15)

At macro n its additional expansion guard is equivalent to

    D_(n+1)−y_(n+1)=c+(y/2)r^(n+1)>0.            (16)

For c≥0 this is strictly positive at every finite n, and the initial-order inequalities at each section also hold: x_n>0, y_n−x_n>0, and D_n−y_n=c+(y/2)r^n>0. Thus all words are valid. If c<0, the right side of (16) is eventually negative, so a finite first guard failure occurs. There is no assumption that the prospective iteration continues physically after that failure. Hence the exact infinite-validity condition on 0<x<y<D is c≥0, including equality.

For c=0, all section coordinates in (15) contract by r, so homogeneity gives T_n=r^nT_0. The total time is T_0/(1−r), which is finite and rational for rational initial data. These are Zeno runs. For c>0, the outer phase alone exceeds 2D_n≥2c at every macro, so total time diverges. These are non-Zeno runs in the very same machine and fixed word.

On D=1 the infinite-validity set is exactly 0<x<y≤2/3; its accepted equality boundary y=2/3 consists entirely of Zeno runs. In gaps, c=g₃−(g₁+g₂)/2, proving Theorem 2. The standard center lies on this Zeno boundary while remaining strictly inside the one-word chamber.

The matrix in (13) has eigenvalues 1,r,r. The invariant c detects the unit mode. Inputs with c=0 use only contracting modes; inputs with c>0 use the unit mode. The determinant r² is positive, consistent with 44-event parity. This is an explicit instance of the active-cyclic-subspace criterion rather than a numerical experiment.

### 9.1 Native positive integer gap certificates

Restrict the input gaps to g₁,g₂,g₃∈Z_{>0}, the native positive-integer domain. Their positivity already supplies the entire initial ordering 0<x<y<D; no additional gap inequalities or auxiliary aliases are required. Define the displayed abbreviation L=2g₃−g₁−g₂. In each polynomial below, L means this literal linear expression in the original three inputs, not another quantified variable.

The mixed-clock classes have the following single-polynomial Diophantine certificates:

* Infinite validity: (2g₃−g₁−g₂−w+1)²=0, with exactly one positive-integer witness variable w. A solution exists exactly when L≥0, and its unique value is w=L+1
* Zeno validity: (2g₃−g₁−g₂)²=0, with no witness variables. It accepts exactly L=0; there is one empty witness tuple on an accepted input and none on a rejected input
* Non-Zeno infinite validity: (2g₃−g₁−g₂−w)²=0, with exactly one positive-integer witness variable w. A solution exists exactly when L>0, and its unique value is w=L

All three polynomials have total degree two and use the native input gaps directly. Over the integers a square vanishes exactly when its base vanishes; the positive-integer witness domain gives the stated weak or strict sign test. These are unique-witness certificates with fully accounted variable counts. The integer-domain qualification matters: allowing w to range over all positive reals or rationals would not make the first formula equivalent to L≥0 for arbitrary real or rational input gaps. No stronger general arithmetic classification is inferred from this elementary example.

## 10 Limits beyond the fixed center

An arbitrary rational homogeneous map M must at least satisfy C∩M⁻¹C≠∅ for an open positive ordered-section domain. Theorem 1 establishes a construction near its specified central eigenray; it does not prove that this necessary compatibility condition is sufficient in general.

A rational finite eigenray (1,p) with M(1,p)=λ(1,p), λ>0, can be moved algebraically to a standard center. If M=[[a,c],[d,B]] and T=[[1,0],[p,I]], then

    T⁻¹MT=[[λ,c],[0,B−pc]].

This permits the fixed-center construction in an explicitly changed rational encoding. It does not by itself implement T or T⁻¹ physically in the original marker coordinates, so it must not be presented as a literal realization of M on the original section. An affine chart change preserving D cannot move a ray at infinity to a finite center. For physical marker meaning in the same positive cone, the chosen ray must be interior and have positive multiplier.

Some positive-cone-compatible rational matrices have no rational fixed ray at all. In positive gap coordinates take

    P_g=[[1,1,1],[1,2,1],[1,1,3]].

It sends every positive gap vector to a positive vector and has determinant 2. Its characteristic polynomial is t³−6t²+8t−2; the only possible rational roots ±1,±2 all fail. Thus it has no rational eigenray and cannot be rationally conjugated into a matrix fixing a rational ray. In centered coordinates it is

    [[4,−1,−1],
     [−1/3,1/3,1/3],
     [−1/3,−1/3,5/3]].

This is a concrete uncovered case, not an impossibility theorem for other signal constructions. No Turing-completeness claim follows from the fixed-center projective compiler.

## 11 Primary literature and claim boundary

The underlying mathematical ingredients have precedents. The bounded source audit in `LITERATURE_AND_SCOPE.md` gives further equation and page detail.

* Mestl, Lemay and Glass, *Chaos in high-dimensional neural and gene networks*, Physica D 98 (1996), §§2 and 4, equations (2.3)–(2.4) and (4.2), derive fixed-itinerary maps x↦Ax/(1+aᵀx) and restrict their domains to the chosen exit walls. This is a close precedent for the normalized algebra, in Glass networks rather than signal machines. [Author/institution-hosted article](https://www.mcgill.ca/physiological-dynamics/sites/physiological-dynamics/files/chaosinhigh_1996.pdf)
* Alishah, Duarte and Peixe, *Asymptotic Poincaré Maps along the edges of Polytopes*, Nonlinearity 33 (2020), §5, give oblique constant-flow projections, inverse maps, and pulled-back itinerary domains. [Primary manuscript](https://arxiv.org/pdf/1411.6227)
* Durand-Lose, *Abstract geometrical computation and the linear Blum, Shub and Smale model*, CiE 2007, §§3.1–3.2, implements arithmetic on scale-relative signal distances. These constructions do not themselves imply this five-live-signal full-section result. [Author manuscript](https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2007_CiE.pdf)
* Becker et al., *Abstract Geometrical Computation 10*, §2, Definitions 1–2, provides the label-dependent speeds and distinct-speed collision convention used here. Five live signals does not mean five meta-signals. [Primary manuscript](https://arxiv.org/pdf/1804.09018)
* Belgacem, Edwards and Farcot, *Computer-aided analysis of high-dimensional Glass networks*, §III, equations (6)–(12), explicitly tracks positive denominators and strict itinerary cones for fractional-linear maps. No associated code was executed. [Primary manuscript](https://arxiv.org/pdf/2411.10451)

This packet's construction-specific result is the exact five-live-signal, rational-speed, number-preserving realization of the stated fixed-center family, together with phase closure, exact chambers, and the 44-event mixed-clock example. There is no novelty, priority, exhaustive-search, general universality, or minimality claim.

## 12 Static evidence and preservation

The new checker implements a small exact polynomial ring over Python standard-library fractions. It verifies 36 symbolic checks, including all eight flight-time and messenger-line identities, the outer restoration equation, the extra guard and its center margin, centered conjugacy, compensated shear, arbitrary-row conjugation with denominators cleared, mixed-clock invariant and nth guard, the exact duration row, and the positive-matrix cubic. Nine rational parameter fixtures verify the inverse parameter relation and compensation; subdivision fixtures include coefficients outside both ends of the direct range. It never chooses a next collision, advances a physical state, or imports an earlier constructor.

These checks support the direct all-parameter proof; they are not a proof-assistant formalization. `evidence/static_checks.json` records the checks and checker hash. `INDEPENDENT_AUDIT.md` independently checks the new chronology, guard, compensation, counts, and mixed-clock example. The two prior proof files are copied unchanged into `dependencies/`, with source hashes in the manifest. All preexisting packets remain untouched.
