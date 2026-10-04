# Exactly five live signals realize every rational orientation-preserving planar map

4 October 2026. Conventional mathematical proof and freshly authored exact/static checks. This packet is separate from, and does not modify, the five-signal rotation-family packet. No upstream/author executable, saved collision schedule, physical trajectory simulator, or old constructor was run. All new executed arithmetic is in the inspected `static_planar.py` in this directory.

## 1. Main theorem

Let A be any 2 by 2 rational matrix with det A>0, and let λ>0 be rational. There is an effectively constructible finite, deterministic, rational-speed, number-preserving one-dimensional signal machine and a fixed complete binary-collision word with the following properties.

* Its outgoing section consists of stationary markers at L=0, x, y, D, with 0<x<y<D, and one messenger at L moving right with speed +1. There are exactly five live signals, including the two outgoing strands at the initial anchor contact.
* In centered coordinates X=x−D/3 and Y=y−2D/3 its return is

      (D,X,Y) ↦ λ(D,A(X,Y)).

* The exact domain of that complete word, on the normalized section D=1, is a bounded open rational polygon P containing 0 in its interior. An explicit finite list of strict rational affine inequalities defining P is produced. They are necessary and sufficient, not merely a safe neighborhood.
* Every marker and messenger returns to its section label and outgoing phase. This permits literal repetition of the same word.
* The normalized infinite-complete-word validity set is exactly

      K(A,P)= intersection over n≥0 of A^(−n)P.

“Fixed” means fixed after A and λ have been chosen. The theorem does not assert one unchanged finite rule table for every A, uniform word length, a minimal number of meta-signals or speeds, or a lower bound excluding fewer live signals. Matrices of negative determinant and singular matrices are outside this realization theorem; no impossibility is claimed for them.

The determinant-one subtheorem uses only signed shear blocks and full anchor transfers. The positive-determinant extension is supplied by a proved centered one-axis dilation; it does not assume a square root of det A or add any live signal.

## 2. Exact primitives and their complete chronology

At any primitive entrance the messenger is at its stationary anchor and points into the interval. During the primitive only one target marker can move. Its speed has modulus strictly less than 1; the messenger has speed ±1. Coordinates in this section are distances to the anchor, so reflection about the right anchor negates all physical velocities and changes no inequalities or times.

### 2.1 Anchor scaling

For u>0, a target initially at distance z is launched with speed

      h=(u−1)/(u+1)

when the outward messenger reaches it. The messenger reverses, bounces at the anchor, returns to restore the target to speed zero, and reverses again to bounce at the anchor. The four principal (time,position) pairs, measured from the primitive entrance, are

      (z,z), (2z,0), (2z+uz,uz), (2z+2uz,0).

Indeed z+h((2z+uz)−z)=uz. Thus the target ends at uz and the duration is 2(z+uz). Denote this operation by L_z(u).

The exact guards say that z and uz lie strictly between the same unchanged nearest stationary neighbors, with the anchor as lower endpoint when the target is nearest to it and no upper endpoint when the target is outermost. If these guards hold, monotonic target motion prevents target/neighbor contact. Every stationary inner marker s is crossed four times, at

      s, 2z−s, 2z+s, 2z+2uz−s.

The hypotheses s<z and s<uz place these in the required outward/inward orders between principal events. There are no outer-marker crossings. The inequalities |h|<1 and positive ordered distances separate all messenger and target contacts. If an endpoint reaches or passes a neighbor, continuity forces an additional or simultaneous target/neighbor contact no later than that proposed endpoint; equality can also collapse prescribed event times. Thus endpoint failure cannot preserve the stated complete binary word.

The nearest target version has four events. With k stationary inner spectators it has 4+4k events.

### 2.2 Reflector homothety

The target at t must be the nearest marker to the anchor. Let z be a stationary reflector beyond it. For v>0, the first outward target hit launches it with speed h=(1−v)/(1+v) while the messenger continues outward. The messenger crosses all stationary spectators between target and reflector, bounces at z, crosses those spectators in reverse, restores the target while continuing inward, and finally bounces at the anchor. Solving its incoming line against the moving target gives

      t'=vt+(1−v)z,
      restoration time=2z−t',
      duration=2z.

Call this H_z(v), with the target understood. Its exact guards are 0<t,t'<s, where s is the nearest unchanged outer marker and s≤z. The target is monotone between its endpoints; it cannot meet a stationary spectator. Every spectator q is crossed at q and 2z−q, in the claimed order because t'<q. The conditions 0<t'<z place restoration strictly between reflector and anchor bounces. Failure of an endpoint gives an extra or coincident contact as in the preceding paragraph. With k intermediate spectators there are 4+2k events.

### 2.3 Translation

For e<1, concatenate L_t(1/(1−e)) and H_z(1−e). This is T_z(e), acting by

      t → t/(1−e) → t+ez.

Both moving phases have speed e/(2−e), strictly between −1 and 1. Its exact guard simplifies to 0<t,t+ez<s≤z. In fact the internal endpoint t/(1−e) lies between t and t+ez. For e>0 this follows from t+ez<z, and for e<0 from t<z; e=0 gives equality of all three target positions. Consequently no extra internal inequality is being discarded. The two primitives preserve the same ordered marker section and messenger-anchor phase.

Even when e=0 or u=v=1, these are genuine nonempty timed collision sequences. The temporary target label then has speed zero; its collision partner still has speed ±1, so the model's distinct-speed condition is satisfied. Identity factors need not be silently removed.

### 2.4 Full anchor transfers

When all four markers are stationary and 0<x<y<D, transfer from L to D by crossing X, crossing Y, then reflecting at D. The three event times are x,y,D, and the final messenger direction is left. Transfer back by crossing Y, crossing X, and reflecting at L; its relative event times are D−y,D−x,D, and its final direction is right. Each transfer has duration D. Its exact condition is the already present strict ordering. A transfer is not a zero-time phase switch.

## 3. Signed centered shear blocks

Write

      U(t)=[[1,t],[0,1]],   V(t)=[[1,0],[t,1]].

For arbitrary rational t choose

      N=max(1,ceil(4|t|)),   δ=t/N.

Thus |δ|≤1/4, including δ=0. A left-anchor micro-shear is

      T_y(δ), followed by T_D(−2δ/3).

It acts on x by x→x+δ(y−2D/3), leaving y,D unchanged, so its centered action is U(δ). The first translation has four L events and four H events. The second has four L events and six H events, including both Y spectator crossings. Each micro-shear has exactly 18 events and four temporary target labels. Its translation parameters satisfy e<1.

For an entire N-step x block, using its incoming coordinates, define

      a_(2k)=x+kδ(y−2D/3),          0≤k≤N,
      a_(2k+1)=a_(2k)+δy,          0≤k<N.

Its exact guards are

      y>0, D−y>0, a_i>0, y−a_i>0 for 0≤i≤2N.

There are 4N+4 supplied rows. The translation lemma makes these endpoint guards necessary and sufficient for all 18N events, including every spectator crossing. Its centered return is U(t).

For a y block, first have the messenger at D pointing left, and set

      r=D−y, s=D−x.

Use exactly the same two translations and endpoint construction in these reflected coordinates: T_s(δ), then T_D(−2δ/3), with D in this notation the distance to the far left anchor. The endpoint distances satisfy r'=r+t(s−2D/3). Hence

      y'=y+t(x−D/3),

so the centered map is V(t), with the same parameter sign, not its negative. Its exact rows are s>0,D−s>0,b_i>0,s−b_i>0, with b_i obtained from the displayed a_i formulas by (x,y)=(r,s). This is again 4N+4 rows and 18N events.

At the center x=D/3,y=2D/3 each micro-shear returns its target, in its anchor coordinates, to D/3. The intermediate translation endpoint is

      D/3+2δD/3 ∈ [D/6,D/2],

strictly between 0 and the unchanged neighbor 2D/3. Every row is therefore strictly positive at the center, independently of the size or sign of the total shear t. Large shears are legitimate finite products of these small steps, not unguarded single jumps.

## 4. Explicit SL₂(Q) factorization, including zero pivots

Let B=[[a,b],[c,d]] and ad−bc=1. Products below act on column vectors; the rightmost factor is performed first.

If c≠0, direct multiplication gives

      B=U((a−1)/c) V(c) U((d−1)/c).

The upper-right entry is (ad−1)/c=b. The chronological block list is x((d−1)/c), y(c), x((a−1)/c).

If c=0 but b≠0, use

      B=V((d−1)/b) U(b) V((a−1)/b).

The lower-left entry is (ad−1)/b=c=0. The chronological list is y((a−1)/b), x(b), y((d−1)/b). This branch requires an initial full L-to-D transfer and a final full D-to-L transfer; omitting either would leave the wrong section phase.

If b=c=0, then a≠0,d=a^(−1), and

      B=U(a−1) V(1) U(a^(−1)−1) V(−a).

The chronological list is y(−a), x(a^(−1)−1), y(1), x(a−1). The formula holds for positive or negative a. No pivot a or d is divided by unless this diagonal branch has established a≠0. It also includes B=I: then the list y(−1),x(0),y(1),x(0) is retained, so the identity target gets a genuine positive-duration closed macro with exact guards. This is not an empty-word exception.

There are therefore B_num=3 or 4 alternating shear blocks. Let K be the sum of their subdivision counts. Keep the messenger at L initially, transfer whenever the next block uses the other anchor, and after the last block transfer to L if necessary. If σ_j is 0 for x and 1 for y, the exact number of full transfers is

      T=σ_1 + sum_(j=1)^(B_num−1) |σ_(j+1)−σ_j| + σ_(B_num).

In the three branches above T is respectively 2,4,4. It is always even, and after these transfers the messenger is at L pointing right with all marker labels restored. The SL₂ word has

      18K+3T events,
      4K+4B_num supplied guards,
      4K temporary marker labels.

This proves the determinant-one physical theorem with full chronology and phase reclosure.

## 5. Centered dilation and the positive-determinant extension

### 5.1 A small rational centered x-dilation

For q in [3/4,5/4], start at L and perform

      L_x(q), then T_D((1−q)/3).

The endpoints are x, qx, and

      x'=qx+(1−q)D/3.

Thus X'=qX, Y'=Y, and D'=D. The physical scale parameter q is positive; the translation parameter e=(1−q)/3 lies in [−1/12,1/12], so all primitive hypotheses hold. The target is X, which remains nearest to L, and the D-reflector translation includes Y as an explicit spectator.

The exact guard rows are

      y>0, D−y>0,
      x>0, y−x>0,
      qx>0, y−qx>0,
      x'>0, y−x'>0.

They are eight supplied rows. They retain the first scale's endpoint qx; the translation's own internal endpoint qx/(1−e) needs no additional row by the translation lemma. At the center these three guarded target endpoints are D/3,qD/3,D/3, with qD/3 in [D/4,5D/12], strictly below 2D/3. The primitive therefore fixes the center and has a full-dimensional center-strict exact chamber.

This operation uses four scale events and ten translation events, hence 14 events and three temporary target labels. It uses the same four markers and messenger as every other operation.

### 5.2 Every positive rational factor, with no irrational roots

For any positive rational q≠1, define

      H=max(1,ceil(4|q−1|/min(1,q))),
      u_j=1+j(q−1)/H for 0≤j≤H,
      q_j=u_j/u_(j−1) for 1≤j≤H.

All u_j are positive rational and at least min(1,q). Consequently

      |q_j−1|=|q−1|/(H u_(j−1))≤1/4.

All q_j therefore lie in [3/4,5/4], and their product telescopes to q. Compose the H small centered x-dilations. The centered action is C_q=diag(q,1), with 14H events, 3H temporary labels, and 8H supplied exact guards. Every completed factor fixes the center, so all pulled-back rows are still center-strict. For q=1 take H=0 and omit these dilation steps.

### 5.3 Assemble the general matrix

For the requested A, let q=det A>0 and set

      B=C_q^(−1)A=diag(q^(−1),1)A.

Then B∈SL₂(Q). First perform the shear realization of B and its final return to L. Then perform the centered x-dilation C_q. The chronological return is C_q B=A, with no further anchor change. This proves the general positive-determinant realization without assuming that √q is rational. In particular it covers nonsquare rational determinants such as 2 or 3/2.

## 6. Optional global homothety and precise counts

For λ<1 append anchor scales in the order X,Y,D, all by λ. An inner neighbor of the currently scaled marker has already been scaled, while an outer neighbor has not. Because the target moves monotonically between z and λz, both endpoints remain strictly between those unchanged neighbors. For λ>1 use the reverse order D,Y,X: outer neighbors are already scaled and inner ones are not. The same argument applies. Thus no extra guard is introduced. The X,Y,D scales have respectively 4,8,12 events, for 24 total, and three temporary labels. For λ=1 omit this suffix.

At completion the centered homogeneous map is N=λ diag(1,A). Let ε be 1 when λ≠1 and 0 otherwise. Including the SL₂ factorization, centered determinant dilation, transfers, and optional global homothety, the counts are

      events m = 18K+3T+14H+24ε,
      supplied guards = 4K+4B_num+8H,
      temporary marker labels = 4K+3H+3ε,
      meta-signals = 22K+3T+17H+27ε+4,
      live signals = 5.

The meta-signal count is m distinct messenger phase labels plus the temporary labels plus four stationary marker labels. Zero-parameter factors are retained in these formulas. No minimization or uniform complexity bound is asserted.

## 7. Exact chamber, first failure, and finite deterministic completion

Pull every row in the preceding block and dilation lists back through the earlier rational homogeneous return maps, using coordinates z=(D,X,Y). Each becomes αD+βX+γY>0 with rational coefficients. Full transfers add no new rows, and the optional global homothety adds none either.

Sufficiency follows inductively from the exact primitive chronology, with all spectator crossings included. All nonmoving markers are stationary, the one moving marker stays in its strict neighbor interval, and the messenger's ±1 speed separates every stipulated binary contact. Hence there are no remote marker contacts or omitted messenger crossings.

For necessity on the positive input section, suppose a supplied row fails. Consider the earliest primitive or translation group whose prospective endpoint checkpoint fails, with all prior endpoints ordered. The preceding complete word prefix is already valid. For an anchor scale, a target must meet or cross its stationary neighbor by the invalid endpoint. For a reflector homothety the same argument applies; its exact restoration equations show that a failed anchor/reflector endpoint can also reverse or collapse a required positive event interval. For a translation group, its internal scale endpoint and final endpoint cannot both remain within the neighbor interval if one of its retained endpoints fails. In every case an extra contact, a simultaneous contact, or a collapsed/reordered prescribed event has occurred by the failed checkpoint. Therefore the specified globally time-separated complete binary word is not realized. Rows that fail at the initial ordered section mean the input was not an allowed initial configuration.

This first-failure argument uses the prospective affine formulas only up to the first obstruction. It does not assume that the desired affine continuation is a physical trajectory after an earlier collision has changed the state.

On D=1, these rows define an open convex rational polygon P. All rows are strict at the center because every completed shear and centered dilation fixes it and all internal center endpoints have been checked. Thus 0 is interior to P. The initial rows of the first block imply 0<x<y<1, even when that first block is right-based: 0<r<s<1 is equivalent to the same ordering. Hence P is bounded. Redundant or repeated rows do not affect these statements.

For the finite rule table, assign the messenger before event j a fresh label Q_j with its prescribed speed ±1, for 0≤j<m. Identify the final outgoing label Q_m with Q_0. Each temporary moving target gets its own label at its rational speed in (−1,1). At event j emit the binary rule

      {Q_j,Z_in} → {Q_((j+1) mod m),Z_out}.

Launch/restoration change the target label; spectator crossings and anchor/reflector bounces retain the relevant stationary marker label. Each input set is distinct because its Q_j is distinct. Incoming and outgoing speeds are pairwise distinct because the messenger has speed ±1 and every marker speed has smaller modulus. Local incoming order is decreasing speed and outgoing order increasing speed, so outgoing strands separate immediately. At the final event, all marker labels are stationary again and Q_0 has speed +1 at L, exactly as at the initial section.

Assign the identity output to every other input set with pairwise distinct speeds. This defines a finite deterministic number-preserving completion, including unprescribed larger collision sets. It cannot turn an extra collision into the selected complete word. Every explicit rule consumes and emits one messenger and one marker, while the completion preserves cardinality too; the live population is exactly five throughout every finite portion of the run. No continuation through an accumulation point is asserted.

## 8. Repetition, time, and the geometry interface

At each completed macro, D is multiplied by λ while normalized w=(X/D,Y/D) is multiplied by A. Since the phase closes exactly, the one-word exact chamber proves

      infinite complete-word validity ⇔ w∈K(A,P)=⋂_(n≥0) A^(−n)P.

The set always contains 0, so infinitely valid inputs exist. No claim is made that P can be chosen arbitrarily while preserving these precise physical counts; P is the exact chamber of this compiler.

Each primitive duration is a rational homogeneous linear form in its incoming coordinates; hence the full duration ℓz is a fixed rational row. Before the final global homothety all positions remain between 0 and D. Each translation takes less than 6D, each micro-shear less than 12D, each centered dilation less than 10D, and each transfer exactly D. The optional global suffix takes less than 6(1+λ)D. Therefore on the exact chamber

      2D ≤ ℓz < (12K+T+10H+6(1+λ)ε)D.

For the lower bound, every retained shear micro-step has a far-reflector H_D phase of duration 2D, and the factorization always has at least one such step, even for A=I. A transfer-based lower bound alone would not cover arbitrary simplified factorizations; this bound does.

At iteration n the scale is D_n=λ^nD_0. Thus every infinitely valid run is Zeno exactly when 0<λ<1. In that case all five signals approach the fixed left anchor, since the n-th macro remains within [0,max(1,λ)D_n]. For λ≥1 the displayed lower bound makes the total time divergent.

For rational initial data and λ<1 the accumulation time is rational, but the expression ℓ(I−N)^(−1)z must not be used blindly: I−N can be singular because A may have an expanding eigenvalue 1/λ, even though no valid orbit uses that mode. Instead let V be the rational cyclic span of z,Nz,N²z. The boundedness of normalized valid orbits gives N^n z→0, so every eigenvalue on V has modulus <1. The rational map I−N is invertible on V, and

      total time = ℓ [(I−N)|_V]^(−1) z

is rational. Equivalently it can be computed by solving a rational linear system on a rational basis of V. The full inverse formula remains valid whenever I−N is nonsingular.

The exact K(A,P) identity is the interface to the companion planar strict-guard spectral classification. This physical theorem does not substitute an invariant polygon or its closure for P, and it preserves every strict-boundary exception. In particular the previously established irrational-rotation phenomenon transfers to all rational matrices conjugate to infinite-order rotations, not just orthogonal matrices in the original coordinates.

### 8.1 Consequence of the companion spectral classification

The companion conventional theorem in `../planar-strict-kernel-classification-20261004/PROOF.md`, Theorem A, applies to this exact P. Combining that theorem with the construction gives a complete criterion throughout this physically realized family:

      K(A,P) is nonsemialgebraic
      if and only if det A=1, |tr A|<2, and tr A is not in {−1,0,1}.

This corollary uses the companion's proof for the nonelliptic direction; the realization theorem above does not depend on it. For the exceptional case the companion constructs a rational positive definite Q with AᵀQA=Q. For each row h_i w<b_i, put d_i=h_i Q^(−1)h_iᵀ, r_i²=b_i²/d_i and p_i=(b_i/d_i)Q^(−1)h_iᵀ. The minimum r² and the deduplicated contacts E of minimizing rows give

      K={w:wᵀQw<r²} union
        ({w:wᵀQw=r²} minus union_(p∈E,n≥0){A^(−n)p}).

These are rational contacts on a rational ellipse; no rational Euclidean conjugating basis is assumed. The finite-order exceptional traces −1,0,1 have orders 3,4,6 respectively and are semialgebraic cases.

The companion's dense accepted and rejected rational tails on the critical ellipse also yield the positive-gap sign obstruction. Because the closed critical ellipse lies inside the closed initial-order triangle, only finitely many of its points fail the strict initial gap conditions. Delete those finitely many from a rejected dense tail; the accepted tail is already inside P. A finite polynomial-sign formula in positive rational gaps cannot separate the two tails. If such a formula agreed on all positive integer gaps instead, replace each atomic polynomial's sign by the eventual sign of its highest nonzero homogeneous component on a positive ray. This finite semialgebraic replacement agrees on every integer ray and hence, by clearing denominators and homogeneity, on every positive rational ray, a contradiction. These statements exclude finite unquantified polynomial-sign classifiers, not Diophantine descriptions with integer witnesses.

For all other realized A, the companion supplies a semialgebraic description using finitely many rational strict/weak guards restricted to the bounded-orbit subspace. That subspace can have an irrational stable direction, so a rational-polyhedral description of the full real set is not claimed. The companion further gives polynomial-time rational membership for every fixed A and input guard polygon; this compiler makes no polynomial-size compilation claim.

## 9. Static evidence and limits

The new standard-library-only `static_planar.py` independently implements the displayed factorization, small-step subdivision, endpoint algebra, complete event grammar, transfers, marker labels, and rational duration rows. It emits a complete binary word and a finite identity-completion declaration. It never selects the next physical collision, compares competing event times, or executes a trajectory. No earlier constructor is imported or executed.

Its fixture suite has 25 rational matrices at each λ in {1,1/2,2}, for 75 full static outputs. It covers all three pivot branches, zero diagonal pivots, identity and negative identity, positive and negative diagonal factors, either shear sign, finite and infinite elliptic order, a nonorthogonal elliptic conjugate, Jordan forms, irrational real eigenvalues, stable and unstable complex spectra, unit-plus-contracting modes, and nonsquare positive determinants.

All 75 pass exact checks for the factorization, telescoping centered dilation, desired endpoint return, every supplied row's positivity at the center, word/guard/type counts, messenger phase continuity including wraparound, all stationary labels restored, even full-transfer closure, and distinct incoming/outgoing collision speeds. Full outputs and their hashes are in `evidence/`; `evidence/summary.json` states the tests. These finite checks support but do not replace the all-parameter proof. There is no proof-assistant certificate, arithmetic witness frontend, determinant-negative obstruction, or claim that the compiler is polynomial-time in the matrix's bit length.

## 10. Relation to prior work and claim boundary

The definition of signal machines, the distinction between meta-signals, live signals and speed count, and the outgoing-collision convention are standard; see Becker et al., *Abstract Geometrical Computation 8*, Definition 1 and the initial-configuration discussion, [primary PDF](https://arxiv.org/pdf/1307.6468). Its small-speed accumulation results concern speed counts, which are not the live-population statement proved here.

Conservative rational translation, scaling, and shrinking already occur in Durand-Lose, *Abstract Geometrical Computation 6*, [author manuscript](https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2012_IJUC_UC_HC.pdf), as documented in the preceding rotation packet's bounded primary-source comparison. The current direct web retrieval of that manuscript failed; no new source verification of it is claimed. The elementary shear factorizations are proved by multiplication here rather than advertised as new linear algebra.

The result supplied by this packet is the explicit extension of the preceding exact five-live-signal construction from rational rotations to every rational positive-determinant planar matrix, with full anchor phase closure, exact strict chambers, and the centered dilation needed for determinants other than one. No exhaustive literature search, priority certification, unrestricted lower bound, universal unchanged finite machine, or minimality claim is made.
