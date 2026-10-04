# A five-live-signal realization of every rational infinite-order planar rotation

4 October 2026. New parameterized mathematical construction, separate from Reports 57 and 58. Conventional proof with exact symbolic/static checks, not a proof-assistant certificate. No old executable, physical simulator, or saved collision schedule was run. The physical constructor emits a finite rule grammar and exact linear endpoints; it does not select or simulate collisions. Arithmetic statements below are literal finite formulas, not a claimed emitted arithmetic frontend or a source-specific gate ledger.

## 1. Theorems and quantifiers

Let a,b,c be integers with c>1, a²+b²=c², and gcd(a,b,c)=1. Define

    R = (1/c) [[a,−b],[b,a]].

These are exactly the rational planar rotations of infinite order. Fix any rational λ>0. There is an explicitly constructible finite rational-speed number-preserving one-dimensional signal machine, with exactly five live signals, and a fixed complete binary-collision macro whose return, in rational homogeneous coordinates (D,X,Y), is

    (D,X,Y) -> λ(D,R(X,Y)).

“Fixed” means fixed after a,b,c,λ are chosen. Neither the finite machine nor its word length is claimed uniform over all rotations. Only its live population is uniformly five. There is no arbitrary-matrix realization claim.

The exact one-macro domain is a finite open rational polygon P on the normalized section D=1, containing the origin. It is obtained effectively from the explicit endpoint rows in Section 4; it is not merely a sufficient safe region. Let ρ be the least distance from the origin to one of its supplied nonconstant guard lines. Let E={p₁,…,p_J} be the distinct perpendicular contact points of all lines attaining ρ. Then J is finite and positive, every p_j is rational, and

    K = ⋂_{n≥0} R^(−n)P
      = {w: ||w||<ρ}
        ∪ ({w: ||w||=ρ} \ ⋃_{j=1}^J {R^(−n)p_j:n≥0}).

This is the exact normalized infinite-complete-word validity set. Its positive homogeneous gap cone is not semialgebraic. More strongly, no finite polynomial-sign formula, even with arbitrary real coefficients, agrees with validity on every positive rational gap triple or on every positive integer gap triple.

Rational membership is nevertheless decidable in deterministic polynomial time in input bit length for each fixed compiled machine, without orbit search. For each fixed rotation and its computed E, validity on three ordinary positive integer input gaps has the explicit existential-positive-integer certificate in Section 8: exactly 1+80J positive witnesses, 1+43J equations, and a sum-of-squares polynomial of exact total degree 12. This uses two explicitly displayed POWER modules per tangency and constructive Pell theorems, not generic MRDP. It makes no finite-fold or unique-witness claim.

Every infinitely valid run is Zeno if and only if 0<λ<1. In that case all signals approach the fixed left anchor, and the accumulation time is rational on rational initial gaps. The λ=1 and λ>1 variants are non-Zeno.

## 2. Elementary rational-rotation facts

Primitive Pythagorean triples with c>1 have a,b nonzero, c odd, and gcd(a,c)=gcd(b,c)=1. For example, if a common prime divided a and c then the equation would force it to divide b; primitivity excludes that. If c were even, parity would force a,b both even or both odd; the first violates primitivity and the second gives 2≡0 modulo 4.

Write ζ=(a+ib)/c. If ζ were a root of unity, ζ+ζ^(−1)=2a/c would be a rational algebraic integer and hence an integer. Since gcd(a,c)=1, this would imply c divides 2, impossible for odd c>1. Thus R has infinite order, and both its positive and negative powers are dense in the rotation group. Conversely the exceptional rational finite-order rotations have entries 0 or ±1 and primitive denominator c=1. This proves the stated parameter coverage.

Put

    t_x = −b/(c+a),      t_y = b/c,
    N_x = max(1,ceil(4|t_x|)),
    N_y = max(1,ceil(4|t_y|)),
    δ_x = t_x/N_x,       δ_y = t_y/N_y,
    K₀ = 2N_x+N_y.

The denominator c+a is positive because |a|<c. Both step parameters are nonzero and have absolute value at most 1/4. With

    S_x(t)=[[1,t],[0,1]],   S_y(s)=[[1,0],[s,1]],

one has

    S_x(t_x) S_y(t_y) S_x(t_x)
      = [[1+t_x t_y, 2t_x+t_x²t_y],[t_y,1+t_x t_y]]
      = R.

Chronologically performing x, then y, then x shears gives this product; the first and last factors coincide, so there is no hidden convention reversal.

## 3. Five signals and complete elementary primitives

The outgoing section has stationary markers L=0, X₀ at x, Y₀ at y, D₀ at D, with 0<x<y<D, and a messenger Q at L moving right at speed +1. Thus there are five live signals, including the two outgoing strands at the left contact. The free positive gaps are

    g=(g₁,g₂,g₃)=(x,y−x,D−y).

The centered homogeneous coordinates are X=x−D/3 and Y=y−2D/3. During each primitive only one marker moves; its speed lies strictly between −1 and +1. All other markers remain stationary. The messenger has speed ±1, and every spectator crossing is included in the prescribed word.

### 3.1 Single-marker scaling L_z(u)

For u>0, let the target start at z>0 and give it speed h=(u−1)/(u+1) when the messenger first reaches it. The messenger reflects left, reflects at L, returns to restore the target to speed zero, then reflects left and returns to L. Every intervening stationary marker is crossed on each applicable leg. The four principal event times/positions are

    (z,z), (2z,0), (2z+uz,uz), (2z+2uz,0).

They satisfy the target line q=z+h(t−z) because h(1+u)=u−1. Hence the target endpoint is uz and duration is 2(z+uz).

The exact guard is that z and uz both lie strictly between the unchanged nearest stationary neighbors of the target, with no upper-neighbor condition when the target is outermost. Sufficiency: the target moves monotonically between those endpoints and cannot meet any stationary marker; |h|<1 makes all messenger separation/catching strict. For an inner stationary marker s below both endpoints, the four crossing times are

    s, 2z−s, 2z+s, 2z+2uz−s,

which occur in the required alternating spatial orders. Necessity: equality at a checked neighbor produces a coincident contact; passage beyond it produces an extra target/neighbor collision by that endpoint. Thus this is complete chronology, not just selected principal events.

### 3.2 Reflector homothety H_z(v)

Here the target at t is the nearest marker to the anchor L, and z>t is a stationary reflector. Let v>0 and h=(1−v)/(1+v). At the outward hit, launch the target with speed h and leave messenger speed +1. It crosses all intervening stationary spectators, reflects at z, crosses them in reverse order, restores the target while retaining speed −1, then reflects at L. Solving the two world lines gives

    t' = vt+(1−v)z,    restoration time = 2z−t',
    duration = 2z.

Its exact guard is that t and t' lie strictly between 0 and the unchanged nearest marker s≤z. Monotonicity excludes target/spectator contacts. Each spectator q between the target and reflector is met at q and 2z−q; t'<q puts its return crossing strictly before restoration. The conditions 0<t'<z make restoration strictly between the reflector and final anchor bounces. Failure of an endpoint condition gives the extra or coincident contact described above.

### 3.3 Translation and reflection

For e<1, perform L_t(1/(1−e)) followed by H_z(1−e). Call this T_z(e). Its positions are

    t -> t/(1−e) -> t+ez,

and both primitives use target speed e/(2−e). If 0<t,t+ez<s≤z, the intermediate position lies between t and t+ez. For e>0 this follows from t+ez<z; for e<0 from t<z; e=0 is the identity case. Therefore the exact translation guard reduces to its start/end ordering, with no additional internal inequality. The physical target is monotone throughout the two primitives.

Reflection in D replaces a coordinate q by D−q, takes D as stationary anchor, and negates all physical velocities. All chronology and exact-guard statements survive unchanged. No H primitive used here has an unlisted stationary marker between its anchor and target.

## 4. Parameterized shear word and exact guard polygon

A left-based pair

    T_y(δ), then T_D(−2δ/3)

acts on x by x->x+δ(y−2D/3), with y,D unchanged. Its first translation uses eight events (four for L and four for H with reflector Y); its second uses ten (four for L and six for H with spectator Y and reflector D). Thus one micro-shear has 18 events.

Repeat this pair N_x times with δ=δ_x. The centered return is S_x(t_x). Transfer the messenger to D by crossing X, crossing Y, and reflecting at D: three events. In reflected coordinates r=D−y and s=D−x, repeat

    T_s(δ_y), then T_D(−2δ_y/3)

N_y times. This gives r->r+t_y(s−2D/3), hence y->y+t_y(x−D/3), the centered S_y(t_y). Transfer back by crossing Y, crossing X, and reflecting at L: three events. Repeat the first x-shear block. The rotation word has

    m_rot = 18K₀+6

events. All translation parameters satisfy e<1 because |δ|≤1/4 and |−2δ/3|≤1/6.

For an x-block with n micro-shears of parameter δ and incoming coordinates x,y,D, define

    a_(2k)   = x+kδ(y−2D/3),              k=0,…,n,
    a_(2k+1) = x+kδ(y−2D/3)+δy,          k=0,…,n−1.

Its exact guards are

    0<y<D,      0<a_i<y for i=0,…,2n.

For the reflected y-block, put r=D−y and s=D−x and define the same endpoint expressions b_i with (x,y) replaced by (r,s). Its exact guards are

    0<s<D,      0<b_i<s for i=0,…,2n.

There are 4n+4 supplied rows per block. Pulling them back through the preceding rational affine block maps gives exactly 4K₀+12 strict homogeneous rational linear rows in (D,X,Y). D>0 follows already from the ordered initial rows; it can also be stated as the ambient section assumption.

These rows are necessary and sufficient for the whole complete word. The primitive lemmas prove sufficiency inductively. For necessity, assume positive initial gaps and take the first failed endpoint checkpoint. All previous primitives have their prescribed order. The target must reach or cross a fixed neighbor by the failed checkpoint, producing an extra or simultaneous collision, or collapsing two prescribed event times. Thus the specified globally time-separated binary word has failed by then. A failed initial-order row instead means that the input is outside the required outgoing section. No failed row is treated merely as leaving a convenient sufficient neighborhood.

At the center x=D/3,y=2D/3 every micro-shear pair returns its target to D/3 in anchor coordinates. Its intervening translation endpoint is

    D/3 + 2δD/3 ∈ [D/6,D/2].

Both bounds are strictly inside (0,2D/3), so every row is strictly positive at the center. This argument repeats for arbitrarily many small steps and either sign of δ. It does not assume the total shear is small.

Let P be the D=1 section in w=(X/D,Y/D). It is open, convex, rational, and contains zero in its interior. Its initial rows include 0<x<y<1, so it is bounded. The rows need not be irredundant.

## 5. Optional rational homothety and the exact return

For 0<λ<1, append L_x(λ), then L_y(λ), then L_D(λ). At each step every inner neighbor is already scaled and every outer neighbor is unscaled. A target moving monotonically from z to λz remains above all scaled inner neighbors and below all unscaled outer neighbors. For λ>1 use the reverse order D,Y,X: every outer neighbor is already scaled and every inner neighbor is unscaled, giving the same strict order proof. For λ=1 omit the homothety entirely.

The X,Y,D primitives have respectively 4,8,12 events, regardless of their chosen order, and their common target speed is (λ−1)/(λ+1)∈(−1,1). The homothety introduces no new guard. It restores all stationary marker labels and the messenger at L moving +1. Its duration is

    2(1+λ)(x_rot+y_rot+D).

Thus m=m_rot if λ=1 and m=m_rot+24 otherwise. The return in (D,X,Y) is N=diag(λ,λR). In ordinary positive gaps the rational return matrix is

    M = λ/(3c) *
      [[c+2a−b, c−a−b, c−a+2b],
       [c−a+3b, c+2a, c−a−3b],
       [c−a−2b, c−a+b, c+2a+b]].

For

    Q = [[1,1,1],[2/3,−1/3,−1/3],[1/3,1/3,−2/3]],

one has QM=NQ. Negative entries of M outside the exact chamber are not a physical claim about an executable return there.

### 5.1 Finite rule table and population

Give each pre-event messenger state a distinct Q_j label for 0≤j<m, with its specified ±1 speed, and identify Q_m=Q_0. Give each of the 4K₀ translation primitives its own temporary target label with the primitive's rational speed. Add three temporary labels when λ≠1. Keep the four stationary labels L₀,X₀,Y₀,D₀.

At event j emit the binary rule

    {Q_j,Z_in} -> {Q_(j+1 mod m),Z_out},

where Z is the encountered marker, with launch/restoration changing between its stationary and temporary label and spectator/bounce events leaving it stationary. For an L primitive, reverse messenger direction at all four principal events; for H, preserve direction at launch/restoration and reverse at reflector/anchor. Include every spectator crossing. The three-event transfers have the stated direction reversal at their final anchor.

Every rule has pairwise distinct input speeds and pairwise distinct output speeds because messenger speeds are ±1 and target speeds have modulus less than one. Each Q_j is used in precisely one explicit input rule, so there are no conflicting prescribed input sets. At binary contacts, incoming local order is decreasing speed and outgoing local order is increasing speed; hence the declared strands separate immediately. The strict endpoint proof keeps all other markers away from that location and excludes remote collisions too.

Assign the identity rule to every other collision input set with pairwise distinct speeds. This is a finite deterministic number-preserving completion. It does not make an extra collision conform to the selected complete word. Every explicit rule consumes and emits one messenger and the same one marker identity. Hence there are exactly five live signals throughout, although the meta-signal count is

    22K₀+10       if λ=1,
    22K₀+37       if λ≠1.

No minimal phase, speed, rule, or word-length claim is made.

## 6. Exact infinite-validity geometry, including multiple tangencies

Write each normalized row as α+v·w>0. Its constant α is positive. Ignore any constant-only row, which is always satisfied. For every other row set

    d_row² = α²/(v·v),
    p_row  = −αv/(v·v).

There is at least one such row because P is bounded. Let ρ² be the minimum of these positive rational numbers and deduplicate the p_row of the minimizing rows to obtain E. Then ρ>0, ρ² is rational, and every point of E is a nonzero rational point of norm ρ. Duplicate rows and distinct rows yielding the same point cause no difficulty.

For ||w||<ρ, Cauchy–Schwarz makes every row strictly positive. For ||w||=ρ, a row can vanish only if it is minimizing and w is its perpendicular contact; all other rows are uniformly strict. Thus on this circle the complement of P is exactly E. For ||w||>ρ, any nearest row is strictly negative on a nonempty open arc of that larger circle. The forward rotational orbit meets that arc by density.

Normalized data always update by R, independently of λ. The exact finite chamber equivalence therefore proves the formula for K in Section 1. On a contact with positive initial gaps, a failed guard has the physical extra/tied-contact interpretation proved above. A contact on an initial-order face is simply not a permitted initial section; its shifted inverse-orbit points are still excluded exactly by the same finite-chamber criterion.

The critical-circle excluded set is countably infinite (one nonzero tangent already has an infinite orbit) and the retained set is uncountable. A semialgebraic subset of a circle is a finite union of points and arcs. Therefore neither that boundary membership pattern nor K is semialgebraic. Slicing the homogeneous gap cone at D=1 proves the real-gap conclusion. Real quantifier elimination also rules out a finite existential-real polynomial description of the exact real set.

### 6.1 Rational sign obstruction without a unique tangent hypothesis

Fix p∈E and consider its full orbit O={R^k p:k∈Z}. Each point of E is either outside O or equals R^k p for one unique integer k, because R has infinite order. Thus

    I={k∈Z:R^k p∈E}

is finite, nonempty, and contains 0. Let k_* be its largest element. Restricted to O, the forbidden union of backward orbits consists exactly of indices k≤k_*. Consequently the forward tail {R^k p:k>k_*} is accepted and dense, while the backward tail {R^k p:k≤k_*} is rejected and dense. All these points are rational. There is no need to solve whether two tangencies share an orbit in order to use this finite-index argument in the proof.

The positive-input domain requires care. The closed radius-ρ disk lies in the closed initial-order triangle. A strict initial-order inequality can vanish on its circle only at one perpendicular contact; hence only finitely many circle points have a zero initial gap. Removing those finitely many points from the rejected tail leaves a dense rejected set of positive rational gap inputs. The accepted tail already has positive gaps, since K⊂P and P includes the strict initial-order rows. Thus both required dense sets live in the allowed positive domain.

A finite polynomial-sign formula restricts on the algebraic circle to a semialgebraic subset, with membership constant on each of finitely many open arcs after finitely many endpoints are removed. Such a set cannot contain every member of the dense accepted tail and exclude every member of the dense rejected tail. This holds even for arbitrary real coefficients.

### 6.2 Positive integer sign obstruction

Suppose a finite Boolean formula F of polynomial-sign atoms were correct on every positive integer gap triple. Write each polynomial f as the finite sum of its homogeneous components f_d. For any fixed g, the eventual sign of f(tg) as t→+∞ is the sign of the highest-degree component nonzero at g, or zero when every component vanishes. This is a finite semialgebraic case distinction, invariant under positive rescaling of g.

Replace each atom in F by its eventual-sign case distinction, obtaining a homogeneous semialgebraic formula F_∞. Along every positive integer ray, the physical predicate is constant and F is assumed correct at every positive integer multiple. Hence F_∞ is correct there too. Clearing denominators and using positive-scale invariance extends agreement to every positive rational gap triple. That contradicts Section 6.1. No homogeneity assumption on the original F was made.

## 7. Exact rational arithmetic and time

Given rational positive gaps, compute w=(X/D,Y/D) and compare ||w||² with ρ² exactly. Accept below, reject above. On equality, for each p_j form the rational Gaussian number

    η_j=(w_x+iw_y)/(p_{jx}+ip_{jy}).

The point is invalid exactly when at least one η_j=((a−ib)/c)^n for n≥0.

For every prime p dividing c, p is odd and p divides neither a nor b. In the quotient ring (Z/pZ)[i] with i²=−1, z=a−ib satisfies

    z²=2az,   hence z^n=(2a)^(n−1)z for n≥1.

Both coordinates on the right are nonzero modulo p. This calculation does not presume that the quotient ring is a field. It shows that neither integer numerator coordinate of (a−ib)^n has any prime factor in common with c. The joint reduced denominator of ((a−ib)/c)^n is therefore exactly c^n, including n=0 with denominator 1.

For η_j, let q_j be its least common positive denominator. If q_j is not a power of c, it cannot match. If q_j=c^n, the exponent is forced; compare exactly with that one inverse power using integer arithmetic. Repeating this finitely for the J contacts decides rational membership. No density argument is used as an algorithm and no unbounded orbit search is required.

### 7.1 Polynomial-time rational membership for a fixed machine

Fix the compiled machine, so c,a,b,ρ² and all J rational contact coordinates are constants. Encode each rational gap by an ordinary binary signed numerator and positive denominator; let L be the total encoding length. Reject malformed or nonpositive gaps by exact sign checks. Reduction to lowest terms is optional initially.

There are only constantly many arithmetic operations in the radius test and in forming each η_j. Products of constantly many input numerators/denominators have O(L) bits, so all resulting reduced fractions and joint denominators q_j have O(L) bits. Integer gcd, exact comparison and reduction take polynomial time; grade-school division with the Euclidean algorithm gives a conservative O(L³) bound for each of this fixed number of such operations.

To recognize q_j=c^n, repeatedly divide by the fixed integer c while divisible. There are at most log_c(q_j)=O(L) divisions, all on O(L)-bit integers. If the remaining integer is not 1, no power matches. Otherwise n=O(L) is forced. Compute (a−ib)^n by n successive multiplications by the fixed Gaussian integer a−ib. Its coefficients have magnitude at most c^n=q_j and therefore O(L) bits at every step. This uses polynomially many bit operations (indeed O(L²) with fixed-coefficient schoolbook multiplication), and the final rational-numerator comparison has the same bounded bit size. Doing this for the fixed J contacts remains polynomial; O(L³) is a conservative whole-procedure bound with elementary arithmetic.

This complexity statement holds the compiled machine and its tangencies fixed. It makes no uniform compilation-cost or parameter-size claim, no optimality claim, and no claim that the potentially enormous Pell witnesses can be found with comparable cost. The decision algorithm does not construct the auxiliary ordinary powers used only in the Diophantine proof.

### 7.2 Zeno classification and clock

The rotation portion contains 2K₀ translation gadgets. Each L part takes less than 4D and each H part at most 2D, so the rotation duration is less than (12K₀+2)D, including the two length-D transfers. With a homothety the extra duration is less than 6(1+λ)D. Thus a uniform bound per macro is

    0 < ℓ(D,X,Y) < C_λ D,
    C_λ = 12K₀+8+6λ,

when λ≠1; the smaller rotation-only bound applies at λ=1. Every duration is a fixed rational homogeneous linear form ℓ, since all primitive duration and endpoint expressions are rational linear.

At repetition n, D_n=λ^n D_0. If λ<1 the total duration is at most C_λ D_0/(1−λ), and every position stays within the initial macro interval [0,D_n], so every strand tends to L. Since the eigenvalues of N have modulus λ<1,

    T(z)=Σ_{n≥0} ℓN^n z = ℓ(I−N)^(−1)z,
    z=(D,X,Y).

All coefficients are rational, giving rational time on rational input. If λ≥1, the two transfers alone contribute 2D_n, whose infinite sum diverges. Therefore the Zeno iff statement is exact. No continuation through an accumulation is asserted.

## 8. Literal finite-arity degree-12 certificate

This section concerns ordinary positive integer input gaps and one fixed machine. The finite contact list E is first computed from its rational chamber; J≥1. Arithmetic constants depending on that machine are fixed coefficients, not inputs or witnesses.

Write ρ²=H/K in positive integer lowest terms. Put

    D=g₁+g₂+g₃,  x=g₁,  y=g₁+g₂,
    A=3x−D,     B=3y−2D,
    Δ=9HD²−K(A²+B²).

Use one natural radius witness d and impose Δ=d. For each j choose fixed integers r_j,s_j and t_j>0 with p_j=(r_j/t_j,s_j/t_j); r_j²+s_j²>0. Define fixed linear input expressions

    U_j=t_j(r_j A+s_j B),
    V_j=t_j(r_j B−s_j A),
    Q_j=3(r_j²+s_j²)D.

Then η_j=(U_j+iV_j)/Q_j, including at the center, and Q_j>0. These aliases are expressions rather than extra witness quantities.

For each j independently introduce natural n,k,L_C,H_C,L_S,H_S; positive h,q,r,s,t,J_acc; and signed u,v,e₁,e₂,e₃,C,S,κ. Let ε=sign(b) and instantiate the explicit POWER equations below twice to define

    P=POWER(c,n),
    β_rad=4P+2c+1,
    T=POWER(a+|b|β_rad,n).

Here β_rad is only a linear expression in P, distinct from a POWER module's Pell parameter β. Impose these thirteen equations for that j:

1. U_j=hu
2. V_j=hv
3. Q_j=hq
4. e₁u+e₂v+e₃q=1
5. q=Pr
6. r=ck+s
7. s+t=c
8. C+P=L_C
9. P−C=H_C
10. S+P=L_S
11. P−S=H_S
12. T−C−β_rad S=κ(β_rad²+1)
13. d²+(r−1)²+(u−C)²+(v+εS)²=J_acc

All domains matter: d and the six per-contact natural quantities may be zero; h,q,r,s,t,J_acc are strictly positive; signed variables are unrestricted integers. Replace a natural z by z_plus−1 with z_plus>0. Replace a signed z by z_positive−z_negative with both positive. Positive quantities remain individual leaves. Every domain conversion is an explicit affine expression.

### 8.1 Why these outer equations are exact

The first four equations say that (u,v,q) is the primitive joint quotient of (U_j,V_j,Q_j): Bézout forces gcd(u,v,q)=1, and h>0 then forces h=gcd(U_j,V_j,Q_j). Because Q_j>0 this includes zero numerator components and the center U_j=V_j=0, where q=1. The Bézout relation also proves that q is exactly the least common positive denominator of u/q and v/q.

POWER gives P=c^n. Equations 6–7 give 1≤s≤c−1 and k≥0; hence r>0 and c does not divide r. Every positive q has a unique factorization q=c^n r of this form, obtained by repeatedly dividing by the integer c. For composite c this is not being called an additive prime-adic valuation; uniqueness and existence are all that is used.

Let C_n+iS_n=(a+i|b|)^n. Its modulus is c^n=P, so both coordinates lie in [−P,P]. The polynomial substitution i→β_rad modulo β_rad²+1 gives

    (a+|b|β_rad)^n ≡ C_n+β_rad S_n (mod β_rad²+1).

The true pair therefore satisfies the extraction equation and bounds. Conversely, for any other bounded C,S the differences obey

    |(C−C_n)+β_rad(S−S_n)| ≤ 2P(1+β_rad) < β_rad²+1.

The strict inequality follows already from β_rad>4P: β_rad²+1−2P(1+β_rad)>8P²−2P+1>0 for P≥1. Divisibility forces that integer difference to be zero. Since |C−C_n|≤2P<β_rad, both differences must be zero. Thus the extracted coefficients are exact. Negative a causes no base problem:

    a+|b|β_rad ≥ −(c−1)+(4P+2c+1)=4P+c+2>2.

The denominator theorem in Section 7 now says that η_j is a forbidden inverse power if and only if r=1, u=C and v=−εS. The sign in the last square is therefore v+εS, not v−εS. The exponent n=0 correctly gives P=1,C=1,S=0 and excludes η_j=1 on the boundary.

The shared radius equation forces Δ≥0. If Δ>0, every final positive J_acc exists automatically. If Δ=0, the final equation for each j is solvable exactly when that j is not a forbidden match. Conjoining all j is precisely the geometric validity predicate. Conversely, for a valid input choose the positive gcds, Bézout coefficients, canonical c-power factors, true complex coefficients, bounded slacks, congruence quotients, and POWER witnesses; then every positive J_acc is the displayed nonzero sum. This proves both directions without a boundary selector or generic MRDP.

### 8.2 Completely expanded POWER module

For an integer base B₀≥2 and a natural exponent e, introduce directly positive

    out,w,M,g,x_p,y_p,u_p,v_p,s_p,t_p,q_b,q_v,J_p,

two positive leaves whose values plus one are α,β (so α,β≥2), and natural

    d_wb,d_wk,d_yk, α₁,α₂, σ₁,σ₂, τ₁,τ₂, r₁,r₂.

Define expressions k₀=e+1 and m₀=B₀*out. The fifteen equations are:

1. x_p²=1+(α²−1)y_p²
2. u_p²=1+(α²−1)v_p²
3. s_p²=1+(β²−1)t_p²
4. β=1+4y_p q_b
5. β+u_p α₁=α+u_p α₂
6. v_p=y_p² q_v
7. s_p+u_p σ₁=x_p+u_p σ₂
8. t_p+4y_p τ₁=k₀+4y_p τ₂
9. y_p=k₀+d_yk
10. w=B₀+d_wb
11. w=k₀+d_wk
12. M=m₀+J_p
13. α²=1+((w+1)²−1)(wg)²
14. 2αB₀=M+(B₀²+1)
15. x_p+Mr₁=y_p(α−B₀)+m₀+Mr₂

After the stated adapters, this is 26 positive leaves, including its output, and 15 equations. Its precise mathematical dependency is the constructive Pell characterization `Pell.matiyasevic` and power characterization `Pell.eq_pow_of_pell`, in mathlib4 commit ac77769fabe23cb237559e7f56578dbead91499f, file Mathlib/NumberTheory/PellMatiyasevic.lean, SHA-256 993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a. Those are theorems being specialized, not unexpanded arithmetic oracle symbols.

For clarity on the specialization: equations 1–9 are the positive-index branch of the constructive Pell-index characterization, with k₀≥1 and y_p≥k₀. They force (x_p,y_p) to be the Pell pair at index k₀ for α. Equations 10–15 specialize the positive-base power characterization, with its strict M>m₀ bound. Equation 13 and w≥B₀≥2 give α>w≥B₀, so the displayed ordinary integer subtraction α−B₀ agrees with the natural subtraction in that theorem. It follows that B₀^k₀=m₀=B₀*out; cancellation gives out=B₀^e.

Conversely the constructive theorems supply these values for B₀^k₀. Their auxiliary g is nonzero since α≥2. Pell x_p,u_p,s_p are positive; y_p≥k₀≥1 and v_p>0 make q_v positive. β>1 and β≡1 mod 4y_p make q_b positive. The congruence t_p≡k₀ mod 4y_p and 1≤k₀≤y_p<4y_p exclude t_p=0. The strict modulus bound supplies J_p>0. Each signed congruence difference is represented by a difference of two natural multiples, as explicitly displayed. Thus the positive domains lose no solutions, and the shift k₀=e+1 includes exponent e=0.

The first family base is c≥5; the second is a+|b|β_rad>2 as proved above. Both satisfy the module hypothesis before its semantic conclusion is invoked.

### 8.3 Fixed arity and exact degree, without a gate claim

There is one shared natural radius leaf. Each contact uses six natural leaves, six positive leaves, sixteen positive leaves for its eight signed values, and two 26-leaf POWER modules. Therefore the ordinary positive witness count is

    1+J(6+6+16+52)=1+80J.

There is one radius equation and per contact thirteen outer plus thirty POWER equations, totaling 1+43J. Define F to be literally the sum of the squares of all these residual polynomials after substituting every alias and domain adapter. This is an explicit finite formula for every fixed chamber; J is a fixed machine-dependent integer, not a witness-indexed array.

All outer residuals have degree at most three jointly in input and independent witness leaves. Each POWER residual has degree at most six, including when its second base is the linear expression a+|b|(4P+2c+1). The thirteenth POWER residual has degree-six leading term −w⁴g². Its square supplies a nonzero degree-twelve contribution. The degree-twelve homogeneous part of F is a sum of squares of real homogeneous polynomials, so cannot cancel identically. Since J≥1, F has exact degree 12.

A paid Cantor decoding can transport this to one positive input: use positive witness gaps g₁,g₂,g₃ and one natural j, and append

    2j=(g₂+g₃−2)(g₂+g₃−1)+2(g₃−1),
    2(z−1)=(g₁−1+j)(g₁+j)+2j.

This adds four positive leaves and two quadratic residuals, giving 5+80J positive witnesses and 3+43J equations, still exact degree 12, for the bijective code z=1+pair(g₁−1,pair(g₂−1,g₃−1)). This optional transported formula has a different input ledger from the native theorem.

No exact gate count or generic emitted arithmetic DAG is claimed here. The positive-pair representation of signed values alone supplies infinitely many witness presentations, so no uniqueness or finite-fold conclusion is warranted.

## 9. Concrete new-family example and verification limits

For (a,b,c)=(3,4,5), this family chooses N_x=2,N_y=4, hence K₀=8. It has 150 events without scaling and 174 with λ≠1; at λ=1/2 it has 213 meta-signals and 44 supplied guards. Its unique nearest row is

    D/5−4X/5+7Y/5>0,

with ρ²=1/65 and p=(4/65,−7/65). This differs from Report 57's larger-step 138-event half-scaled machine, whose radius squared is 4/1845. Even at the same return matrix the finite chamber and infinite-validity predicate differ. The theorem does not silently substitute this machine for that earlier machine or its 81-witness certificate.

`static_family.py` is the newly written exact symbolic constructor. Its `construct(a,b,c,lam)` output is a JSON-serializable dictionary containing parameter fractions, counts, the gap return matrix, rational duration row, all named guard rows, exact squared inradius, nearest-row records and deduplicated tangencies, primitive phase ranges, the complete label/speed map, every indexed binary rule, and the identity-default declaration. Fractions are serialized as integer or numerator/denominator strings. Input validation enforces the primitive Pythagorean conditions and λ>0.

The fixture runner constructs 15 signed/order-sensitive triples at each λ∈{1,1/2,2}, giving 45 static outputs. It checks center positivity of every row, the shear return, the conjugacy QM=NQ, phase continuity, event/guard/label counts, pairwise distinct collision input/output speeds, rational nearest contacts, and nonnegativity of all rows at all nearest contacts. These finite checks support the parameterized proof; they do not replace it. The constructor never computes an event time to select a next event and never executes a physical trajectory.

The arithmetic review is separate and checks composite c, negative a, either orientation, zero exponent, domain adapters, witness counts and degree. Its finite arithmetic tests do not instantiate general enormous Pell witnesses; the all-exponent POWER equivalence is the stated constructive theorem dependency. The family arithmetic frontend has not been emitted or independently source-audited as a circuit.

## 10. Prior work and claim boundary

Geometric multiplication/division, rational conservative signal arithmetic, shrinking and Zeno accumulation are established techniques. Abstract irrational-rotation obstructions to semialgebraic separation are also prior work. The candidate result here is the uniform-five-live-population physical realization of the full rational infinite-order rotation family, with exact complete-word chambers, their precise strict-boundary deletion formula, and the explicit fixed-arity arithmetic specialization. It is not an exhaustive novelty claim.

The primary-source comparison is recorded separately in PRIOR_WORK.md. Especially relevant are Durand-Lose's conservative stack/shrinking constructions (AGC6), and Fijalkow–Ohlmann–Ouaknine–Pouly–Worrell, *Semialgebraic Invariant Synthesis for the Kannan–Lipton Orbit Problem* (STACS 2017), Example 1, whose rational rotation (1/5)[[4,−3],[3,4]] already exhibits failure of semialgebraic separation of an unreachable circle target. Earlier three-variable linear-loop nonsemialgebraicity also precedes this work. Fixed-five meta-signal or five-reference-marker counts in earlier papers must not be confused with exactly five total live signals throughout a number-preserving macro.
