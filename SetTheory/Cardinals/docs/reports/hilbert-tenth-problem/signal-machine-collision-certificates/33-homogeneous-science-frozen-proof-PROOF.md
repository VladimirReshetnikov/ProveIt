# Exact local realization of compatible rational homogeneous maps with five live signals

4 October 2026. This is a new proof packet, preserving the earlier packets. It proves the missing physical translation lemma and then completes the local full-homogeneous criterion. Its dependencies are included as unchanged text. No author/upstream mathematical program, physical simulator, or saved collision schedule is executed. Freshly authored, inspected static algebra is supporting evidence only.

## 1. The criterion and its precise scope

The outgoing section consists of stationary markers L=0, X=x, Y=y, R=D, with 0<x<y<D, and one messenger at L outgoing at speed +1. There are exactly five live signals, counting both outgoing strands at the initial L/messenger contact. Set

    z=(D,ξ,η)ᵀ,    ξ=x−D/3,    η=y−2D/3.

The ordered open cone and its normalized triangle are

    C={z: D/3+ξ>0, D/3+η−ξ>0, D/3−η>0},
    Ω={w∈R²: (1,w)ᵀ∈C}.

The three cone inequalities imply D>0. The centered origin 0 belongs to Ω.

**Theorem.** Let N be a rational 3×3 matrix. In the full-section, binary, distinct-incoming-and-outgoing-speed model just specified, the following are equivalent:

1. A finite deterministic rational-speed number-preserving signal machine has a nonempty positive-duration complete binary word that returns literally to this section and acts by z↦Nz on some nonempty full-dimensional open set.
2. det N≠0 and C∩N⁻¹C≠∅.

When (2) holds, there is an effective construction of the machine, its word, and a finite exact list of strict rational homogeneous guard rows Gz>0. Its exact chamber Q={z:Gz>0} contains a rational ray (1,p) with p∈Ω. On D=1 the chamber is a bounded nonempty open rational polygon. The construction realizes the requested homogeneous representative N itself, rather than only its projective class. It restores every stationary marker label and the initial outgoing messenger phase.

The claim is local one-pass realizability on the standard original marker section. It does not say that every input of C∩N⁻¹C realizes the selected word, that a prescribed guard polygon is realizable, that the constructed chamber is forward invariant, or that any infinitely valid input exists. Nor does it provide one unchanged finite rule table for all matrices, polynomial-size words, optimal counts, global reversibility, or continuation after an accumulation. No Turing-completeness or novelty claim is made.

## 2. Precisely inherited results

The preserved `dependencies/fixed_center_PROOF.md`, Theorem 1 and §§2–6, together with its fresh accepted review `dependencies/fixed_center_REVIEW.md`, gives this interface:

    For rational s>0, b∈Q^(1×2), A∈GL₂(Q),
    M=[[s,b],[0,A]]

has a nonempty literal five-signal complete-word realization with a finite exact rational homogeneous guard list strict at e₀=(1,0,0)ᵀ. The supplied word has positive duration, and fresh phase copies may be used at interfaces. The construction includes the orientation-reversing primitive when det A<0. It is not merely a conjugated encoding.

The preserved `dependencies/invertibility_PROOF.md`, Theorem A and §§2–4, proves that every full-coordinate fixed complete binary-word return under the theorem's hypotheses is invertible. It applies to the three translation-quotiented section coordinates (D,ξ,η). Its parity theorem gives sign(det return)=(−1)^m for a literal m-event return in the fixed section chart.

We use and re-establish below the nearest-target translation chronology from `dependencies/positive_planar_PROOF.md`, §§2.1–2.4. Earlier executable constructors are not needed or invoked. The fixed-center compiler's full exact guards, rather than just its endpoint guards, are retained in the composition.

## 3. A ten-event physical nearest-target translation

Use distance coordinates from a stationary anchor, with a nearest target at t, nearest unchanged outer marker at s, and a far stationary reflector at D. In the four-marker section there is exactly one stationary spectator between this nearest target and the far reflector. Let e<1 be a fixed rational parameter, and set

    u=t/(1−e),    t′=t+eD,    h=e/(2−e).

Assume exactly the endpoint guards

    0<t<s<D,    0<t′<s.                         (1)

Since e<1, −1<h<1. First scale the target about its anchor by 1/(1−e). Then perform a reflector homothety of ratio 1−e about the far reflector. Each uses a fresh temporary target label, even when e=0.

The first four event times/positions, starting with the messenger at the anchor pointing outward, are

    (t,t), (2t,0), (2t+u,u), (2t+2u,0).

At event 1 the target is launched with distance velocity h and the messenger reverses; event 2 bounces the messenger at the anchor; event 3 restores the target and reverses the messenger; event 4 bounces the messenger at the anchor. The target restoration equation is t+h(t+u)=u. No spectator lies between this nearest target and the anchor.

Put α=2t+2u. The next six event times and messenger positions are

    (α+u,u), (α+s,s), (α+D,D),
    (α+2D−s,s), (α+2D−t′,t′), (α+2D,0).

At the first of these, launch the target with the same h while the messenger continues outward. Cross the spectator, bounce at the reflector, cross the spectator inward, restore the target while continuing inward, and bounce at the anchor. The restoration identity is

    u+h[(2D−t′)−u]=t′.

The internal restored endpoint u lies between t and t′. Indeed

    u−t=e t/(1−e),
    t′−u=e(D−t′)/(1−e).

Both right sides have the sign of e under (1); for e=0 both vanish. Hence 0<u<s. All four scale flights and all six homothety flights are strictly positive. In the second part the flight lengths are

    u, s−u, D−s, D−s, s−t′, t′.

Within either moving phase the target moves monotonically between two points of (0,s), so it cannot collide with the anchor, spectator, or reflector. The messenger has speeds ±1 and the target has speed h∈(−1,1); its prescribed departure and return are transverse. The six listed crossings exhaust every spectator contact. There is no other moving marker. Thus (1) gives complete chronology, not just correct endpoints.

Conversely, after an initially valid ordered section, if a required endpoint leaves (0,s), the prospective continuous target segment reaches an adjacent stationary marker, or a prescribed event interval collapses/reorders, no later than the proposed restoration. If the first scale is already obstructed, stop there; otherwise the same argument applies to the homothety. This is a first-failure argument, and never runs a trajectory through an earlier wrong collision. Therefore (1) is the exact guard for this ten-event word.

This operation, denoted T_D(e) with its target understood, changes t to t+eD and changes no other stationary-marker position. It returns the messenger to its anchor pointing into the interval. Its duration is

    2[t+t/(1−e)]+2D.                            (2)

It is strictly between 2D and 6D on its exact chamber. At e=0 it remains a genuine ten-event timed identity. Speed-zero temporary labels are valid because their actual collision partners have speeds ±1.

Reflection about R negates all physical velocities and changes none of these distance-coordinate times, inequalities, or counts.

## 4. Physical translation of any rational interior shape to another

For a∈Q² define the homogeneous shape translation

    T_a=[[1,0,0],[a₁,1,0],[a₂,0,1]].

It fixes D and acts by w↦w+a. This section proves a physical realization rather than making a coordinate substitution.

**Translation lemma.** For every rational p,q∈Ω, there is a literal complete-word realization of T_(q−p) with exact rational chamber containing (1,p). The construction can be selected to have 26n events and 4n fresh temporary marker labels for an explicit positive integer n.

Write

    γ₁(w)=1/3+w₁,
    γ₂(w)=1/3+w₂−w₁,
    γ₃(w)=1/3−w₂.

Let m be the minimum of the six positive numbers γ_i(p),γ_i(q), and put

    Δ=q−p,    M=max(|Δ₁|,|Δ₂|),
    n=max(1,ceil(2M/m)),    δ=Δ/n.              (3)

All quantities are exact rational data except the explicitly computed positive integer n. Since the γ_i are affine, every point of the straight segment p→q has all gaps at least m. Also m≤1/3 and |δ_j|≤m/2≤1/6. In particular δ₁<1 and −δ₂<1, as required for both primitive translations.

For k=0,…,n−1, execute the following four blocks:

1. From L, use T_D(δ₁) on nearest target X: ten events. Its effect is x↦x+δ₁D, with y,D fixed
2. Transfer L→R by crossing X, crossing Y, and reflecting at R: three events, duration D
3. From R, use reflected T_D(−δ₂) on nearest target Y: ten events. Its distance r=D−y changes to r−δ₂D, so its physical position changes to y+δ₂D, with x,D fixed
4. Transfer R→L by crossing Y, crossing X, and reflecting at L: three events, duration D

At the nominal input w=p, the completed-step positions are p+kδ. The intermediate X-first corner is

    c_k=p+kδ+(δ₁,0).

Its gaps are those of p+kδ plus respectively δ₁,−δ₁,0. Therefore each is at least m/2>0. Both successive translations have ordered initial and final endpoints; their hidden scale endpoints need no new rows by §3. The transfers require only the stationary section ordering already retained. Thus every intermediate contact and flight is legitimate at the nominal input.

Let

    H=[[1/3,1,0],[1/3,−1,1],[1/3,0,−1]],
    Hz=(x,y−x,D−y)ᵀ.

The exact supplied homogeneous guard list for the entire translation is

    H T_(kδ) z>0                       for k=0,…,n,
    H T_((k+1)δ₁,kδ₂) z>0              for k=0,…,n−1.       (4)

There are 6n+3 supplied scalar rows, including redundant rows. Each of the 2n+1 three-row groups is a full ordering test at one completed-step or X-first checkpoint. Formula (4) is necessary and sufficient: apply the exact primitive guards to the first invalid checkpoint after a valid prefix. Initial and final order alone would not justify ignoring the intermediate corners. Formula (4) retains them explicitly.

All rows are strictly positive at (1,p), so their finite intersection contains a full-dimensional open neighborhood of this ray. The maps of the n steps multiply to T_δ^n=T_Δ. Each step restores all stationary labels and returns the messenger to L outgoing right, with no instantaneous phase-switch event. It uses exactly 10+3+10+3=26 binary events and four temporary marker labels. Fresh messenger phases are used at all internal interfaces. A standalone n-step translation can therefore use 26n messenger labels, 4n temporary target labels, and four stationary labels, totaling 30n+4 meta-signals. These are construction counts, not minima.

For p=q, retain n=1, δ=0. This supplies a nonempty 26-event identity; it has four temporary labels, some of speed zero. An identity translation may instead be omitted only when another nonempty macro supplies the timed return.

The duration of a step entering at (D,x,y) is, from (2),

    6D+2(1+1/(1−δ₁))x
       +2(1+1/(1+δ₂))(D−y).                    (5)

The X-first change does not change the Y target's incoming distance D−y. The two scale parts are positive and less than 4D each, hence 6D<T_step<14D. For a full translation, D remains fixed, so 6nD<T_translation<14nD on its exact chamber.

## 5. Left/right normalization completes the proof

Suppose det N≠0 and C∩N⁻¹C≠∅. The intersection is open, so it contains a rational point. By positive normalization of its first coordinate it contains e_p=(1,p) with p∈Ω rational. Write

    N e_p=s(1,q)ᵀ,    s>0,    q∈Ω∩Q².

Define

    N₀=T_(−q) N T_p.                           (6)

Then N₀e₀=se₀. Consequently N₀ has the exact form

    N₀=[[s,b],[0,A₀]],    det A₀=det N/s≠0.     (7)

More explicitly, if N=[[a,b],[c,B]], then s=a+bp, q=(c+Bp)/s, and A₀=B−qb. All quantities are rational. No rational eigenray of N is needed: p is an admissible input shape and q its generally different output shape.

Execute chronologically:

    physical translation p→0,
    the preserved fixed-center compiler for N₀,
    physical translation 0→q.

Their matrices multiply in the actual execution order to

    T_q N₀ T_(−p)=N.                           (8)

This is a left/right normalization, not a conjugacy, and both translations are actual five-signal complete words in the original physical coordinates. Thus (8) is not merely an encoding argument.

Let the exact guard matrices of these three words be G₋,G₀,G₊. The full exact chamber is

    G₋z>0,
    G₀T_(−p)z>0,
    G₊N₀T_(−p)z>0.                             (9)

The first list is strict at e_p by the translation lemma. At e_p the middle word starts at e₀; its own complete guard list is strict there. The last word starts at se₀, and its guards are homogeneous and strict at e₀, so they are strict at se₀. Hence every row in (9) is strict at e_p.

Sufficiency of (9) follows by completing each of the three exact words. For necessity, use the first word with a failed exact guard after a successful prefix. No prospective formula is used after that failure. The first input ordering rows bound the D=1 section by Ω, so (9) defines a bounded open rational polygon containing p. The final physical ordering implies Q⊂C∩N⁻¹C; equality is neither claimed nor needed.

Conversely, suppose such a realization of N exists on a nonempty full-dimensional open chamber. The fixed-word full-section theorem makes its ambient homogeneous positional map invertible. Since it agrees with N on an open set, that ambient map is N, so det N≠0. An input in the chamber and its output are both in the required ordered section, giving C∩N⁻¹C≠∅. This proves both directions.

### 5.1 Phase closure, deterministic rules, and population

Each messenger-involving event receives a fresh incoming messenger phase label with its prescribed rational speed. Its rule outputs the next phase. Only the last outgoing phase of the full composite is identified with the first. Stationary section marker labels have the same roles throughout. Every target launch/restoration uses fresh temporary labels, including zero-speed identity operations. Thus block interfaces do not accidentally identify unrelated standalone messenger rules.

Every new translation event has incoming and outgoing distinct speeds because its messenger speed is ±1 and its target speed lies in (−1,1), or its partner is stationary. The optional seven-event orientation-reversing component within the middle compiler has one marker-only event; its messenger phase must remain unchanged at that event. Give its temporary marker label a fresh copy to isolate that input set, as established by the preserved compiler.

All prescribed rules consume two and emit two signals. Complete the finite rule table by identity rules on all other admissible finite label sets with pairwise distinct speeds. This completion is finite, deterministic, and number-preserving; it does not turn an unlisted contact into part of the chosen word. Exactly five live signals are present throughout each valid finite execution. No global injectivity of the rule map is asserted.

If the selected translations use n₋ and n₊ steps and the fixed-center compiler uses m₀ events, t₀ temporary marker labels, and g₀ guard rows, the composite uses

    m=26(n₋+n₊)+m₀,
    t=4(n₋+n₊)+t₀,
    g=(6n₋+3)+g₀+(6n₊+3).

If r is its number of marker-only events, fresh labels can be counted as m−r+t+4. In the inherited chosen compiler r≤1. Both translations have determinant 1 and even length; therefore sign(det N)=(−1)^m is inherited from the middle block, as required.

## 6. An exact polynomial-time endpoint compatibility decision

The inverse gap-coordinate matrix is

    H⁻¹=[[1,1,1],[2/3,−1/3,−1/3],[1/3,1/3,−2/3]].

Put K=HNH⁻¹. Then C∩N⁻¹C≠∅ is equivalent to existence of g with g>0 and Kg>0. By scaling, impose 1ᵀg=1. Solve the rational linear program

    maximize ε
    subject to 1ᵀg=1,
               g_i≥ε and (Kg)_i≥ε  (i=1,2,3),
               0≤ε≤1.                         (10)

The compatibility condition holds exactly when (10) is feasible with a positive optimum. If a strict positive g exists, normalize it and choose ε>0 below all six coordinates. Conversely any feasible ε>0 is a strict witness. An infeasible program or optimum zero means incompatibility. When feasible, the set is compact: g lies in the closed standard simplex and ε in [0,1]. Therefore an optimum exists.

No black-box numerical tolerance is needed. There are four variables, one equality, and eight inequalities. Enumerate the at most C(8,3)=56 triples of inequality boundaries, solve with the equality whenever the four rows have full rank, retain candidates satisfying every weak inequality, and choose the greatest ε. A nonempty compact polytope has a vertex, including in its lower-dimensional cases, so this procedure finds the exact optimum or proves infeasibility. Every arithmetic operation is rational and the dimension and number of constraints are fixed. Cramer's rule or exact Gaussian elimination gives polynomial bit complexity in the rational input length. Computing det N is also polynomial.

A positive rational optimizing vertex gives g and then

    e_p=H⁻¹g,
    s=1ᵀKg>0,
    q=((H⁻¹Kg)₂,(H⁻¹Kg)₃)/s.

The first coordinate of H⁻¹g is 1, so the lower two coordinates are p. This provides every input required by §§4–5.

This is a polynomial endpoint-feasibility and realizability *decision*. It is not a polynomial output-size claim for the collision word. The translation count can scale like a reciprocal interior margin, and the inherited rational compiler can also have large subdivision counts. Small binary descriptions can therefore yield large explicit words in this selected construction.

## 7. The previously uncovered positive-gap matrix

Consider

    K=[[1,1,1],[1,2,1],[1,1,3]],
    N=H⁻¹KH=[[4,−1,−1],
             [−1/3,1/3,1/3],
             [−1/3,−1/3,5/3]].

Here det K=det N=2. All strictly positive gap vectors are sent to strictly positive vectors. The characteristic polynomial t³−6t²+8t−2 has none of its possible rational roots ±1,±2, so K and N have no rational eigenray.

Nevertheless choose p=0. Then Ne₀=(4,−1/3,−1/3)ᵀ, giving

    s=4,    q=(−1/12,−1/12),
    N₀=[[4,−1,−1],
        [0,1/4,1/4],
        [0,−5/12,19/12]].

The lower block has determinant 1/2, so it is admitted by the fixed-center theorem. For the physical suffix 0→q the minimum endpoint gap is m=1/4 and M=1/12. Formula (3) gives n=1. Thus one 26-event physical translation after the N₀ compiler gives N exactly. The initial p→0 identity may be omitted because the middle compiler is nonempty; alternatively it may be retained for uniform bookkeeping. This explicitly closes the rational-eigenray gap rather than assuming it away.

At the nominal D=1 initial point, the middle compiler finishes at scale 4 with x=4/3,y=8/3. The suffix first moves X to 1, then Y to 7/3, keeping R=4. Its intermediate and final orders are strict. Its normalized final gaps are 1/4,1/3,5/12.

## 8. An explicit degree-six positive-integer Diophantine representation

This corollary concerns local physical realizability just proved, not infinite repetition.

Let K=(k_ij) be a 3×3 **integer** matrix in gap coordinates and let q be a fixed or externally supplied positive integer denominator. Its rational homogeneous return is K/q in gap coordinates. Positive common scaling does not affect either nonsingularity or the positive-cone compatibility test. Define, with positive integer witnesses

    g₁,g₂,g₃,h₁,h₂,h₃,b,d,

the single integer polynomial

    F(K;g,h,b,d)
      = Σ_(i=1)^3 ((Kg)_i−h_i)²
        + [det K−(2b−3)d]²
        + [(b−1)(b−2)]².                        (11)

**Claim.** F=0 has a positive-integer witness tuple if and only if the represented rational return is locally physically realizable on the standard five-signal section.

Because every summand is a nonnegative integer square, F=0 forces Kg=h>0. It also forces b∈{1,2}, so det K=−d or +d and is nonzero. Thus the theorem's two conditions hold. Conversely strict real feasibility gives a positive rational g, by openness of rational strict linear inequalities. Clear a common positive denominator to obtain g∈Z_(>0)³; then h=Kg is also a positive integer vector. Select b=1 when det K<0 and b=2 when det K>0, and let d=|det K|. All five residual equations vanish.

The exact ledger of (11) is:

- Nine signed integer matrix-entry inputs; an optional positive denominator input does not occur in the polynomial
- Eight positive-integer witnesses
- Five squared residual equations: three vector coordinates, one determinant/sign equation, and one two-value gate
- One resulting polynomial of exact total degree six, because the cubic determinant is squared; the other displayed terms have degree at most four

Every signed entry k_ij may be represented externally as a_ij−c_ij with a_ij,c_ij positive input leaves. This changes the matrix-entry input interface from nine signed inputs to eighteen positive external inputs; it adds no witnesses and leaves the exact degree six. If the positive denominator is included as an input, count it separately. No minimality or finite-fold statement is made. Indeed, if one witness tuple exists, replacing (g,h) by (rg,rh) for any positive integer r gives infinitely many witness tuples, with b,d unchanged.

### 8.1 Explicit centered-coordinate input conversion

If instead the user's native signed integer numerator is M in centered coordinates, so N=M/q with q>0, the fixed change of coordinates must be accounted for explicitly. Define

    S=3H=[[1,3,0],[1,−3,3],[1,0,−3]],
    B=3H⁻¹=[[3,3,3],[2,−1,−1],[1,1,−2]].

Then SB=BS=9I, and the **integer** matrix K̃=SMB satisfies

    H(M/q)H⁻¹=K̃/(9q),    det K̃=729 det M.     (12)

Thus a native centered-coordinate polynomial is obtained by the explicit substitution K=SMB in (11):

    F_center(M;g,h,b,d)
      = Σ_i (((SMB)g)_i−h_i)²
        + [729 det M−(2b−3)d]²
        + [(b−1)(b−2)]².                        (13)

There are still exactly nine signed matrix-entry inputs, eight positive witnesses, five squared residuals, and exact total degree six. The fixed linear substitution introduces no hidden witnesses or alias variables. Eighteen positive external input leaves may again encode the nine signed numerator entries by differences. The constant denominator factor 9 is positive and adds no condition.

This is an explicit Diophantine representation of this particular decidable matrix property, using the theorem to identify it with local realization. It is not a general Diophantine normal-form or undecidability theorem.

### 8.2 Literal native arithmetic DAG and exact operation ledger

`CERTIFICATE_DAG_SIGNED.json` emits a literal binary arithmetic DAG for (11). Leaves are the nine signed entries, eight positive witnesses, and constants 1,2,3. Each square is one multiplication, multiplication by the fixed constant 2 is counted, and gate outputs are unrestricted integers. This is an arithmetic expression graph, not a physical collision schedule and not an extra collection of Diophantine witnesses.

The selected graph uses these operations:

- Three row dot products: 9 multiplications, 6 additions
- Three row residual differences: 3 subtractions
- Cofactor determinant k₁₁(k₂₂k₃₃−k₂₃k₃₂)−k₁₂(k₂₁k₃₃−k₂₃k₃₁)+k₁₃(k₂₁k₃₂−k₂₂k₃₁): 9 multiplications, 1 addition, 4 subtractions
- Sign value 2b−3: 1 multiplication, 1 subtraction
- Multiplication of that sign by d and subtraction from det K: 1 multiplication, 1 subtraction
- Binary gate residual (b−1)(b−2): 1 multiplication, 2 subtractions
- Five residual squares: 5 multiplications
- Sum of the five squares: 4 additions

Total: **26 multiplications + 11 additions + 11 subtractions = 48 binary operations**. The full ordered node list and final output identifier are emitted, not only the aggregate count.

`CERTIFICATE_DAG_POSITIVE.json` prepends the nine actual differences k_ij=a_ij−c_ij. Its ledger is **26 multiplications + 11 additions + 20 subtractions = 57 binary operations**, on eighteen positive external matrix-entry leaves and the same eight positive witnesses. The denominator remains an optional unused positive input.

These two operation counts are explicitly for native **gap-coordinate** inputs. They do not silently include or make free the centered-coordinate conversion SMB of §8.1; no literal operation count is asserted here for that centered-input graph. Formula (13) does explicitly account for its polynomial input substitution, witness count, and degree. Neither emitted native count is a minimum, a record, a universal representation comparison, or a measure of the much larger physical signal-word compiler.

## 9. Repetition and clocks: conditional consequences only

Let Q={z:Gz>0} be the actual full chamber (9). Literal phase closure gives

    infinite validity of this complete word
      ⇔ G N^n z>0 for every integer n≥0.        (14)

The chamber need not be forward invariant, and the set in (14) can be empty. For an explicit endpoint obstruction in gap coordinates, take

    K_escape=[[1,0,0],[0,1,0],[−1,0,1]].

It has determinant 1 and is compatible on g₃>g₁>0, g₂>0. But its nth iterate has third gap g₃−ng₁, so no strictly positive input remains in the ordered cone forever. The theorem realizes its centered conjugate locally, while **no** repeated realization of that same full return can have an infinitely valid input. This rules out an implicit infinite-validity conclusion from one-pass compatibility.

If both physical translations are retained, including an identity when necessary, the first translation takes more than 6D. Every event time and endpoint coordinate is a fixed rational homogeneous linear form on Q. The closure of the normalized input triangle is compact, so finitely many such forms give an effective finite upper bound on duration and all intermediate positions, proportional to incoming D. Thus the full duration ℓz has rational ℓ and constants c₁,c₂>0 such that

    c₁D≤ℓz≤c₂D on Q,    with c₁=6 available.  (15)

For any **infinitely valid** input z, put z_n=N^nz and D_n=(z_n)₁>0. The same elementary active-cyclic-space argument used in the preserved fixed-center proof now gives

    Zeno ⇔ Σ_n D_n<∞ ⇔ N^nz→0
         ⇔ every eigenvalue of N restricted to
            span(z,Nz,N²z) has modulus <1.      (16)

For clarity, ΣD_n<∞ implies z_n→0 because ordering bounds |ξ_n| and |η_n| by constants times D_n. Conversely z_n→0 means the cyclic invariant subspace generated by z has only strictly stable generalized eigenspaces; polynomial-times-geometric Jordan bounds make Σ‖z_n‖ finite. Inequality (15) then proves (16). If z is rational and the execution is Zeno, the total time is rational using the inverse of I−N on that rational cyclic subspace. An ambient inverse is unnecessary and may fail if unused unit modes exist.

All clock claims are conditional on (14). They provide no decision procedure for the general infinite-validity set and no continuation at accumulation. The local realizability theorem does not depend on this optional corollary.

## 10. Primary-source positioning and evidence boundary

The following primary sources were inspected again for this packet. They establish the surrounding model and geometric/arithmetic precedents, rather than the specific five-live-signal criterion proved here.

1. Becker et al., *Abstract Geometrical Computation 10: An Intrinsically Universal Family of Signal Machines*, §2, Definitions 1–2, PDF pp.4–5. Finite labels carry constant speeds; each collision's incoming and outgoing sets have distinct speeds; the operational next-event definition uses the smallest positive meeting time. Equal speeds on labels used in different phases are allowed. [Primary manuscript](https://arxiv.org/pdf/1804.09018)
2. Alishah, Duarte and Peixe, *Asymptotic Poincaré Maps along the edges of Polytopes*, §5, equation (5.2), Proposition 5.4 and Definition 5.7. Oblique constant-flow section maps, their itinerary domains, and composition along a path supply close geometric precedents. Their setting is polytope flows. [Primary manuscript](https://arxiv.org/pdf/1411.6227)
3. Durand-Lose, *Abstract geometrical computation and the linear Blum, Shub and Smale model*, §§3.1–3.2. Scale-relative signal-distance arithmetic supplies relevant arithmetic precedent; that construction does not by itself imply this population-preserving full-section theorem. [Author manuscript](https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2007_CiE.pdf)

The construction-specific result is the exact criterion in §1, obtained by the physically implemented translations and left/right reduction in §§3–5, plus the explicit local-realizability Diophantine representation in §8. There is no novelty, priority, exhaustive-search, universality, or minimality claim.

The freshly authored `static_algebra.py` is inspected before execution. It checks symbolic translation identities, gap-coordinate changes, the generic left/right matrix identity, exact endpoint LP fixtures, translation-corner margin fixtures, the previously uncovered matrix, the escaping-gap example, and the native Diophantine ledgers. It imports no earlier constructor, selects no next collision, and executes no stored machine schedule. The conventional all-parameter proofs above are essential; finite arithmetic checks do not replace them or constitute proof-assistant formalization.
