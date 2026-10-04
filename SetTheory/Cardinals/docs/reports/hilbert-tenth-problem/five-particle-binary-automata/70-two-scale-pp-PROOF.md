# Two-scale recognition: a source-uniform radius reduction

Date: 2026-10-04. Status: mathematical proof packet with independent proof audit passed. This is a new full-shift rule, with unchanged admissible simulation; it is not a numbered article, a minimal-radius result, or an external novelty claim.

## 1. Statement and dependency boundary

For every finite source satisfying the authenticated Report26 source interface, there is a binary, translation-equivariant, ordinary finite-number-conserving full-shift CA F*=P26 after E*, where E* and P26 are each full-shift involutions, of sufficient radius

    R* <= 108D+149+3J, where D=2m+4p.

Its forward and inverse actions equal Report26's rule on the entire admissible doubled micrograph. Consequently its valid mass is exactly five, and its encoding, physical microedge clock, reflections, halt observer, and clean-target construction are unchanged.

The literal finite template families and encoding are those of authenticated COMPILER_PROOF.md Sections3–6. This packet specifies a different globally enforced edge-block selection procedure. Source semantics is needed for admissible agreement; full-shift involutivity is enforced by construction and does not rely on source semantics on malformed configurations.

For the prior universal ledger m=122622,p=66066,J=0, D=509508 and R*<=55,027,013. This is a substitution in a source-uniform proved bound, with the same universal-source dependency as Report26's91,711,698. The universal source table is pinned in the original receipt but not contained or executed here. No universal truth table, interpreter, new arithmetic verifier, or circuit-cost bound is claimed.

## 2. Abstract two-scale lemma

Write I_t(u)=[u-t,u+t] intersect Z. Fix integers 0<=b<=a<=r. Let rho(x,u) be a translation-covariant Boolean predicate determined by x|I_a(u), and R(x)={u:rho(x,u)}. For each u let T_u be the translate of a fixed everywhere-defined configuration involution, with the following properties:

- T_u writes only I_b(u)
- Its output on I_b(u) is determined by x|I_r(u)
- It preserves the sum of bits on I_b(u)
- T_u(x)!=x implies rho(x,u)

Set H=max(2(b+a),b+r). Select u in S(x) if u in R(x), no other v in R(x) satisfies |v-u|<=H, and R(T_u x)=R(x). Define A coordinatewise by applying every selected local replacement simultaneously; outside all selected write intervals leave x unchanged.

### 2.1 Finite definition and prospective test

Changing I_b(u) can affect rho(x,v) only for |v-u|<=b+a. Hence R(T_u x)=R(x) is equivalent to finitely many predicate comparisons on that anchor interval. Once T_u is known, these comparisons use only I_(b+2a)(u). Determining T_u itself uses I_r(u). Selected centers are farther apart than H>=2b; their write intervals are disjoint. Thus A is well-defined even on arbitrary bi-infinite configurations.

### 2.2 Recognition invariance, including cooperative candidate births

Any recognition window I_a(v) meets at most one selected write interval. If it met intervals centered at u and w, then |u-w|<=2(b+a)<=H, contradicting selection. Its input after A is therefore either its original input or precisely the input after one T_u. In the latter case the prospective test at u guarantees its recognition value is unchanged. Thus R(Ax)=R(x). In particular, two distant changes cannot jointly create an otherwise absent recognition anchor.

### 2.3 Local control and eligibility invariance

Fix any anchor u that is recognized and isolated, whether selected or not. Every selected w!=u has |w-u|>H. Because H>=b+r, its write interval misses I_r(u), the full local-control read window. Because H>=2b+2a, it also misses I_(b+2a)(u), the full prospective-comparison input window. Therefore other selected updates cannot alter T_u's local choice or its prospective test.

If u is unselected, nothing changes in either determining window, so it stays unselected. If u is selected, its own update interchanges x and T_u x in the prospective equality, since T_u is an involution. That equality remains true. Recognition invariance preserves recognized status and isolation. Nonisolated recognized anchors remain nonisolated; absent anchors remain absent. Consequently S(Ax)=S(x).

This proof includes T_u=id at a recognized anchor: it passes the prospective test, but writes nothing, and its identity choice is unchanged because other selected writes miss I_r(u). It also includes arbitrarily many overlapping recognition windows and arbitrary patterns of rejected anchors.

### 2.4 Full-shift involution, conservation, and radius

The second application selects exactly the same anchors. At each such u, the control read window contains its own previous local image and no modification from any other selected anchor. Applying T_u again restores the original bits. Hence A^2=id on the full binary shift. Disjoint equal-weight replacements conserve the number of ones on every finite configuration. The rule is translation-covariant.

An output coordinate can be written only by anchors within b. Isolation uses H+a about such an anchor; local control uses r; prospectivity uses max(r,b+2a). Since H+a dominates both latter bounds, A has radius at most

    b+a+max(2(b+a),b+r).

## 3. A globally reversible local choice among same-anchor templates

For each Report26 edge template g, retain its type-specific write set W_g=I_(B_g)(0), equal-weight distinct endpoint words P_g,Q_g, and exact guarded predicate c_g(x,u). Let tau_(g,u) transpose the endpoint words on u+W_g, acting as identity on all other words and elsewhere. Each tau is an everywhere-defined equal-weight involution.

At a fixed anchor define C_u(x)={g:c_g(x,u)}. Define T_u by the following fully specified rule:

- If C_u(x)={g} and C_u(tau_(g,u)x)={g}, return tau_(g,u)x
- Otherwise return x

There is no priority rule or arbitrary tie-breaking. Before/after uniqueness uses ALL edge-template types at u. The condition is symmetric across tau_g; if it holds at x it holds at tau_g x with the same g, and tau_g^2=id. If it fails, the input is fixed. Hence T_u is an involution on every configuration, including malformed ones with zero, multiple, or newly enabled candidate types.

All c_g read radius at most r=Z+J, and each write interval lies in I_b(u). Evaluating a hypothetical c_h(tau_g x,u) does not enlarge the input radius: bits inside the rewrite are computed from the known endpoint substitution, while every unchanged bit is already in I_r(u). Therefore T_u reads only r and writes only b. It conserves ordinary finite mass.

## 4. Short-range raw-anchor recognition

For every g define rho_g(x,u) to mean: the particles in I_(3B_g+1)(u) are exactly u+P_g or u+Q_g. Omit the contextual guard and keep each type's own exactness window. Put rho(x,u)=OR_g rho_g(x,u). Distinct geometric types at the SAME INTEGER ANCHOR contribute one recognized anchor, not competing keys. This predicate has radius a=3b+1. Since c_g implies rho_g, T_u(x)!=x implies rho(x,u).

Use the abstract lemma to define E*. This construction is independent of whether the source guards have disjoint domains or images. Those source assumptions are required only in Section6 to guarantee the intended valid transition is not rejected.

## 5. Resource calculation

Keep the original constants:

    D=2m+4p; S=2D+2; B2=D+1; L=3D+4;
    b=B3=4D+5; Z=10b+10+2J;
    a=3b+1; r=Z+J=10b+10+3J.

Then b+r=11b+10+3J >=2(b+a)=8b+2. Hence

    H=b+r;
    R_edge* <=b+a+H=5b+Z+J+1=15b+11+3J.

The original Report26 phase block P26 has radius12b+3 and is a full-shift involution. Therefore

    R(F*) <=R_edge*+R(P26)
           <=27b+14+3J
            =108D+149+3J.

No compiler or universal template array must be run to establish this arithmetic. The number of template types remains8pD+29p+m+a_source; Boolean evaluation complexity is not bounded by the count of two blocks.

## 6. Source assumptions and all-admissible agreement

The finite source is deterministic and partial-injective on ALL natural-counter IDs: branch domains at a control are disjoint; exact branch image domains at a target control are disjoint; enabled updates preserve natural counters. Domain and exact image guards depend on classes0,...,J,>J. The designated halt control has no outgoing branch. Clean targets additionally use the prior control-wide predecessor-free initial normalization and wrapper, without changing this lemma.

The admissible doubled micrograph consists exactly of all home IDs over natural counters and the strict intermediate configurations of ENABLED source-edge subdivisions, with both signs and all translations. Geometric but guard-invalid intermediate packets are not assumed admissible.

### 6.1 Recognition uses the correct particles

Every admissible configuration has one close pair of gap<=D, the head; all head-marker distances exceedD and all marker separations are at leastZ. Every pair template is a head pair, and every triple template has one close pair and a singleton separated from both pair sites by more thanD. Therefore every raw match uses the actual head pair. Its signed gap determines its signed mode. A fixed triple cannot contain two markers, because its diameter<=2b<Z. More strongly, every possible edge triple places its singleton within distance L+1 of the actual head anchor; two different markers cannot support competing raw triple matches because Z>2(L+1). Signed-mode restrictions and the disjoint intervals below then resolve competing template types. Other markers are outside its type-specific exactness window, including at a shifted reverse endpoint, since Z-1>3b+1.

### 6.2 Homes and same-anchor competing branches

At a plus home H_q+, only outgoing dispatch/direct forward orientations match geometrically, all anchored at the origin. At a minus home H_q-, only incoming commit/direct reverse orientations match geometrically, all anchored at the origin. No moving-mode pair or travel template has that signed gap. Thus raw recognition is either empty or the singleton origin, even when many branch types share the same home endpoint.

The guarded set C_origin is empty or a singleton by the source's domain/image disjointness. Its selected endpoint has the same g and origin anchor after the swap. Exact reverse image predicates ensure the endpoint lies in the admissible subdivision. The mutual-uniqueness test consequently accepts the unique desired edge; with no desired edge T is identity. Removing guards for recognition alone does not introduce a second raw anchor.

### 6.3 All moving boundaries

Orient a corridor in forward head direction w, with departure marker A and arrival marker C, N=w(C-A)>=Z, and t=w(x-A). Then S<=t<=N-S. Geometric raw matches partition plus states as follows:

- Behind travel: S<=t<=L, anchor A
- Free travel: L+1<=t<=N-L-1, anchor x
- Ahead travel: N-L<=t<=N-S-1, anchor C
- Forward interaction: t=N-S

For minus states the free key is x-w, not x. The geometric partition is:

- Reverse interaction: t=S
- Behind inverse travel: S+1<=t<=L+1, anchor A
- Free inverse travel: L+2<=t<=N-L, anchor x-w
- Ahead inverse travel: N-L+1<=t<=N-S, anchor C

The intervals are disjoint and exhaustive. In particular, a behind triple arriving at minus t=L+1 blocks free inverse recognition because its predecessor anchor still sees the departure marker atL. An ahead free move from distanceL+1 ends at minus distanceL, while reverse ahead triples end at distanceL-1. No travel template competes at either interaction wall.

Forward O interaction is the endpoint template at the old selected marker; reverse O interaction is dispatch at the origin. Forward I interaction is commit at the origin. Reverse I interaction is the endpoint template anchored at the OLD marker coordinate m=m'-v*Delta, possibly one site from the current marker m'. The endpoint's singleton offset v*Delta forces exactly that same old anchor in both orientations. Branch-specific signed O/I gaps exclude other interactions. Dispatch/commit guards hold because these intermediates belong to enabled branches.

Thus at every moving admissible state there is exactly one raw anchor, and the intended transposition preserves that raw singleton. At homes raw recognition can have several types but still only one anchor. On both endpoints of every intended microedge, the guarded type set at that anchor is the same singleton{g}; hence T_u equals the intended transposition.

### 6.4 Passing the new full-shift safety filter

The recognized-anchor set is empty or singleton on every admissible edge-block input. At a desired edge it is the SAME singleton at both endpoints. Hence isolation and prospective recognition invariance hold automatically. At missing edges T_u is identity regardless of recognition. E* therefore equals Report26's edge matching on the entire admissible doubled graph. P26 is unchanged, and both restricted blocks preserve that graph. Consequently F* and its inverse agree step for step with Report26 there.

The original clock tau_e(c)=3+2(Z+c)+Delta-4S for nonzero source updates and one step for zero updates is unchanged. The anchored observer length remains3D+3. The previous clean-target first-time2Theta+2 and reflected-period4Theta+6 conclusions transfer on their original hypotheses.

## 7. Scope and comparison

Report26 used guarded type-keys for recognition and one common radius r. This gave exclusion2(b+r), edge radius3(b+r), and total180D+258+9J. The new construction uses short raw-anchor recognition plus a longer reversible guard-controlled choice, yielding a smaller sufficient radius while retaining the same encoding geometry and exact admissible timing. It generally changes behavior on malformed configurations; no equality with the old full-shift rule or automatic transfer of old malformed certificates is asserted.

The largest remaining scale is unary head-mode encoding: D distinct signed gaps encode2m+4p modes. Lowering this source count or changing finite-mass head coding would be a different project and may change clocks. The present theorem reduces the coefficient without modifying the universal source or requiring a new source universality proof.

## 8. Explicit malformed-input inequality with Report26

Take the two-control source q,h with one true-guard right-increment branch q->h and J=0. Its literal signed-mode order is H_q+,H_q-,H_h+,H_h-,O_e+,O_e-,I_e+,I_e-, with gaps1 through8. In particular O_e has plus gap5 and minus gap6. Here D=8,b=37,Z=380,a=112,r=380. Put

    X={0,5,500,505}.

The two close pairs are too far apart to form any triple template. The only edge candidate/raw anchors are0 and500, both of free O_e type. The relevant free endpoints are{0,5}<->{1,7} at anchor0, and their500-translate. Report26's edge exclusion is834, so both original candidates are rejected. The new exclusion is417, so both raw anchors are isolated. Their local guarded choice is unique in both orientations, and each hypothetical swap preserves the raw anchors{0,500}. Therefore

    E26(X)=X;
    E*(X)={1,7,501,507}.

The unchanged phase block has exclusion298. Its two free O_e phase swaps are isolated and prospectively stable in both cases. Thus

    F26(X)={0,6,500,506};
    F*(X) ={1,6,501,506}.

This exact finite local-rule calculation proves that the new full-shift rule is genuinely different. X has four particles and no valid marker triple, so it is outside the admissible five-particle simulation. The calculation was derived directly from inert endpoint formulas and independently checked; no scientific simulator was run.
