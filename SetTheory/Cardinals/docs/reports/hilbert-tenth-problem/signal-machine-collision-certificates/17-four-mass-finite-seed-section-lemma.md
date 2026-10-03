# Effective finite-seed scattering section at mass four

This note works only in the stationary-unit frame G of radius S>=1. It uses the proved mass-three theorem, including its effective full orbit profiles. It does not claim that original-frame timed or anchored reachability is Presburger.

## 1. A finite library and a single noncircular constant

Let E be the finite set of normalized connected mass-three configurations, where components join occupied sites at distance at most 2S. Every e in E has diameter at most 4S. Including all mass-three configurations of diameter at most 4S instead would make no difference.

For each e, compute the mass-three orbit profile. Put it in exactly one of the following forms after an effectively computed time T_e:

(C) Compact translated-periodic: G^(T_e+r+kp_e)(e) = tau_(kD_e) C_(e,r), 0<=r<p_e, k>=0.

(E) Emitted head: G^(T_e+r+kp_e)(e) is the disjoint union of a stationary unit at a_e and tau_(kD_e) H_(e,r), where H_(e,r) has mass two and diameter at most 2S, and D_e != 0.

If the mass-three theorem supplies a separated head with zero drift, absorb it into (C), with D_e=0. In case (E), increase T_e by a whole number of periods until, at every phase, the head lies strictly more than 2S from a_e on the sign(D_e) side. This is possible because D_e is nonzero. Thereafter its distance from a_e increases by |D_e| every period. This deals with delayed emission: all earlier detachments, returns, and finite excursions remain in the finite prefix. If repeated detachments and returns occur forever as part of a translated-periodic three-mass orbit, they belong to (C), including every phase and the maximum excursion.

Choose an integer B>=4S that bounds the absolute value of every occupied coordinate in all the following finite data, relative to the seed's normalized left edge:
- every prefix time 0<=t<T_e;
- every C_(e,r) in case (C);
- a_e and every H_(e,r) in case (E).

Increase B if needed to be at least 1. This is effective, finite, and depends only on G. In case (C), every phase has diameter at most 2B. In case (E), the initial head-to-residual-marker offset has magnitude at most 2B.

Set N=4B+12S and W=N+2B. These constants are noncircular: first construct the finite seed library, then B, then N and W. B is not taken over mass-three configurations of diameter W.

## 2. Safe resolution of a local encounter

Suppose an actual configuration consists of tau_a(e), e in E, and a fourth unit at b, with |b-a|>B+2S. Until T_e, the isolated seed support lies inside [a-B,a+B], at distance >2S from b. Exact independence therefore proves that the actual configuration is G^t(tau_a(e)) plus the fixed unit b throughout that prefix, including T_e. There is no unobserved influence from the fourth unit.

In case (C):
- If D_e=0, the compact profile and b remain independent forever.
- If D_e points away from b, they remain independent forever.
- If D_e points toward b, follow the compact profile until its first occupied site lies within 2S of b. Before and at that time, independence gives the exact orbit. At that time the complete mass-four configuration has diameter at most 2B+2S<W, irrespective of whether the local rule actually changes either object at that instant. Thus this is a genuine bounded global reset.

The first-contact time exists in the toward case. A bounded support drifting from one side of b to the other cannot cross b without coming within 2S: each occupied output site is within S of some occupied input site. It is effectively computed from finitely many affine phase inequalities. Intermediate configurations are retained by the profile.

In case (E), the source marker is p=a+a_e and the emitted head is receding from p forever. If the fourth unit is on the opposite side from sign(D_e), the entire future is the independent union of the head and two stationary units. If it is on the sign(D_e) side, and n=|b-p|>N, this is a live emission section: a periodic mass-two head at a bounded offset from one endpoint of two stationary markers, moving toward the other endpoint. If n<=N, the emission configuration has diameter at most N+2B=W and can instead be recorded as an ordinary bounded state.

For initial seeds with total configuration diameter >W, the safety condition is automatic: since seed diameter<=4S, |b-a|>W-4S>B+2S. At an emission from such a seed, n>W-4S-B=N+B-4S>=N (strictness is preserved). Thus an outside-W initial local encounter either has a terminal tail, reaches a bounded global state, or produces a live emission section.

## 3. A live section and its next scattering

A live emission section records:
- which stationary marker is the source (left or right);
- the finite seed/emission type and periodic phase;
- the left marker coordinate L;
- the distance n>N to the right marker.

The head's relative position and mass-two shape at the section are fixed by its finite type. Its entire free flight is an isolated finite-phase mass-two profile. It remains independent of the source marker by construction. Stop at first distance <=2S from the target marker. The head plus target marker is then a connected mass-three seed e', of diameter<=4S. Let a' be its left edge. Since the target marker lies in that seed, |a'-b|<=4S. The source marker p therefore satisfies

|p-a'| >= n-4S > N-4S > B+2S.

Consequently the entire next local prefix through T_(e') is independent of the source marker. This is the central uniform guard; it excludes missing a fourth-unit interaction during a long but fixed transient.

For arithmetic bookkeeping, tag the entry seed with the target marker's position within it. This is a finite tag. It matters when the incoming head itself consists of two unit symbols: an untagged three-unit shape does not say which unit was the old target. No extra physical label or memory is being assumed.

If e' has an emitted-head tail, its residual unit is p'=a'+a_(e'). Hence

p'-b = (a'-b)+a_(e'),   |p'-b|<=4S+B.

Only the target marker moves, by this bounded offset. The old source marker remains fixed. Since n>N>B+4S, marker order cannot reverse. Therefore the new marker distance is n'=n+c and its left coordinate is L'=L+d, with c,d drawn from a finite set depending on the finite entry type. If the new head points outward, its tail is terminal. If it points toward the other marker and n'>N, this is the next live section. If n'<=N, its emission configuration lies in the finite normalized W-bounded set.

If e' has a compact tail, the previous subsection applies to that compact mass-three gadget and the old source marker. It either yields a completely explicit independent tail, or reaches a W-bounded full mass-four state. Carrying the target marker for an unbounded duration never produces another unbounded two-marker section before this reset: all three local mass units stay within diameter 2B throughout the compact tail. At the first approach to the remaining marker, all four masses have bounded span.

## 4. Residues and bounded updates

For a live type q with head period P and nonzero displacement D, reflect coordinates if needed so D>0. In phase r, write the head's left edge as p+h_r+kD and its diameter as d_r<=2S. Contact with target p+n is exactly

n-2S-d_r <= h_r+kD <= n+2S.

This hull test is exact: because the head diameter is <=2S, the union of the radius-2S neighborhoods of its occupied sites is the entire expanded interval from its left edge minus2S to its right edge plus2S. The finite set of occupied sites can alternatively be used directly. Because n>N>2B+2S, all candidate cycle counts are in the eventual regime. For every residue rho mod D, the first contact has

h_q(n) = P (n-rho)/D + eta_(q,rho),

a'=b+zeta_(q,rho),

for effectively computed integer constants eta,zeta and a fixed tagged entry seed e'(q,rho). Existence follows from finite propagation; choose the earliest valid phase candidate. Thus the next finite state, c, and d depend only on q and n modulo a fixed modulus. A common multiple of all finite head displacements makes these residue tests part of finite control.

The total macro duration is affine in n on each residue class, plus the fixed local prefix duration. A compact-gadget trip to the other marker similarly has affine-on-residue duration and a bounded target-relative endpoint. Every intermediate configuration in either type of macro has a finite disjunction of affine phase descriptions in L,n and one free-flight cycle variable. No macro is discarded merely because its endpoint is simple.

## 5. Exhaustiveness from arbitrary configurations

Any mass-four configuration decomposes into 2S-components with mass partition among

4; 3+1; 2+2; 2+1+1; 1+1+1+1.

Each component is bounded: a component of mass m has at most m occupied sites and diameter at most 2S(m-1). Therefore:
- A mass-four component lies in the W-bounded ordinary set.
- A 3+1 state uses the finite seed resolution above unless the full configuration is already W-bounded.
- In 2+2, the two components have independent finite-phase motion until first proximity <=2S; that meeting has total span<=6S<W. If no meeting occurs, the two finite-phase profiles describe the entire tail.
- In 2+1+1, the units are stationary and the head has finite-phase motion. Compute its first proximity to either unit. If none occurs, the whole tail is explicit. At contact, either all four masses form a bounded component, or there is a connected mass-three seed and one remaining unit. A total span<=W is ordinary; otherwise the finite seed resolver applies.
- Four mass-one components are fixed.

First contacts in 2+2 and 2+1+1 are effectively computed by finitely many affine phase inequalities, including transient times and taking the earliest valid event. The exact independent profiles describe every precontact time.

Ordinary normalized states of diameter<=W form a finite set. Take one exact CA step from such a state. If still W-bounded, retain that transition. Otherwise its normalized successor has diameter<=W+2S, so there are only finitely many outgoing configurations to precompute by the exhaustive dispatch just given. Their outcomes are terminal profiles, ordinary bounded states, or live sections with fixed initial gap and coordinate offsets. This completes a global effective section system without assuming a uniform bound on arbitrary mass-three inputs.

## 6. Scope and a useful caution

This proves that every indefinitely recurrent unbounded four-mass computation has at most one surviving geometric counter at the scattering section. Its counter and left-marker coordinate receive bounded additive updates with residue guards. A mass-three carrying phase terminates or returns all four masses to a finite normalized state; it does not implement multiplication of a surviving gap.

This alone is not an original-frame anchored reachability theorem. When F^t=tau_(delta t) G^t, elapsed time contributes delta t to every absolute coordinate. Repeated growing-gap shuttles may have quadratic accumulated time. Such time and coordinate observations use the additional arithmetic argument supplied in the report’s original-frame observation section.
