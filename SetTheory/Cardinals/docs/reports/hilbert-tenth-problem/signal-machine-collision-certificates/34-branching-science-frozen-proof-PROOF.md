# A full-section, nondestructive five-signal test and a uniform two-counter compiler

4 October 2026. This packet preserves all earlier packets. It gives explicit physical collision rules, exact open chambers, and uniform encoded-state guards. No author/upstream scientific program, physical simulator, saved collision schedule, or proof assistant is run. A fresh, inspected rational row checker supplies arithmetic evidence only.

## 1. Result, model, and historical scope

A section consists of four stationary markers

    L=0, X=x, Y=y, R=D,   0<x<y<D,

and one messenger at L outgoing at speed +1. Thus there are exactly five live signals, including the two outgoing strands at the section contact. Marker labels are literally restored at every instruction section. A finite control label carried by the messenger may change from one instruction to the next. Labels have fixed rational speeds; equal speeds for labels that do not meet are permitted. Every collision on an encoded run is binary with distinct incoming and distinct outgoing speeds, and successive events have positive time separation. The rule table is deterministic and number preserving.

**Theorem.** For each fixed finite deterministic two-counter program built from increment, zero-test/positive-decrement, and halt instructions, one can effectively construct one finite rational-speed rule table which simulates that program for every pair of nonnegative integer initial counters, using exactly five live signals and this same fixed ordered section. No parameter-dependent rule-table changes occur during a run or when its initial counters change.

Use the rational encoding

    x=D(1/20+(1/10)2^(-a)),
    y=D(19/20-(1/10)2^(-b)).                       (1)

The scale D is unchanged. One simulated nonhalting instruction transition has at most 32 binary collisions and duration strictly between D and 10D. All geometric guard inequalities hold uniformly for every encoded state. Consequently an infinite simulated computation has no finite-time collision accumulation.

The construction contains a reusable **nondestructive test**: on either

    P_Z={x>0, 4x<y<8x, y<D},
    P_N={0<8x<y<D},                               (2)

The test returns exactly the same D,x,y and stationary labels, while outputting one of two distinct outgoing messenger phases. It takes respectively 14 or 12 events. The two branches are selected by actual collision partners, not by remotely changing any label. The explicit inequalities (3) below are the definitive chamber definitions.

**Important historical limitation.** Five-live-signal counter simulation is already present in substance in Durand-Lose's MCU 2004/2005 construction: two fixed scale signals, one signal for each counter at alpha·2^(-a), beta·2^(-b), and one instruction signal, with cardinality-preserving rules. Its marker ordering changes with the counter values and a zero counter lies beyond its unit-scale marker. We do not claim a new five-signal universality result or a minimum population. The concrete result here is the fixed ordered full section, a nondestructive finite branching primitive, explicit strict chronology on its two selected chambers, and one encoding with uniform coverage by every instruction guard. The local realization theorem of Report 63 alone did not establish any of those global coverage or branching claims.

A fixed universal counter program, if chosen, gives a single finite table of this form. This is distinct from claiming one table executes every counter program without an encoding/interpreter. No universal counter program is constructed or optimized here.

## 2. A real branch from a faster returning messenger

We first let the test change X. Section 4 physically undoes that change while retaining the branch in messenger labels. Only L, X, Y and the messenger participate; R is an untouched spectator.

### 2.1 Labels and finite rules

The stationary labels are L,X_0,Y,R. Moving X labels are

    X_pre : -1/2,   X_fast : +2,   X_post : -1/2.

Messenger labels and speeds are

    Q_0:+1, Q_1:-3/2, Q_2:+1, Q_3:-1/4, Q_4:+4,
    C_Z:-1, C_N:-1.

All these labels are distinct even when their speeds agree. The rules before the final anchor bounce are

    {Q_0,X_0}       -> {Q_1,X_pre},
    {Q_1,L}         -> {Q_2,L},
    {Q_2,X_pre}     -> {Q_3,X_fast},
    {Q_3,L}         -> {Q_4,L},
    {X_fast,Y}      -> {X_post,Y},
    {Q_4,X_post}    -> {C_Z,X_0},
    {Q_4,X_fast}    -> {C_N,X_0}.

At an L contact, C_Z and C_N output distinct speed +1 phases. For a standalone changing test they can be arbitrary Q_Z and Q_N. For the nondestructive test, they output the respective reverse-entry labels specified in §4. There is no instantaneous extra event at the interface.

The branch information is acquired in {Q_4,X_post} versus {Q_4,X_fast}. In the first case X has already contacted Y and changed its own label; in the second it has not. The marker-only X/Y collision leaves the messenger label unchanged.

The two exact selected chambers are

    P_Z: x>0, y-4x>0, 8x-y>0, D-y>0,
    P_N: x>0, y-8x>0, D-y>0.                    (3)

These imply the initial section ordering. At y=4x the messenger/L and X/Y contacts are simultaneous at different positions; at y=8x a three-signal contact occurs. Neither boundary is used. The machine also has a lower post-contact chamber x<y<4x, but it is not part of the test interface proved or needed here. In particular, the two complete words certified below do not hide a remote tie.

### 2.2 Common setup

Starting at time 0, the first three events have the following times and positions. L=0, Y=y and R=D throughout.

| Event | Time | Messenger position | X position | Contact |
|---|---:|---:|---:|---|
| Initial outgoing section | 0 | 0 | x | L,Q_0 |
| 1 | x | x | x | Q_0,X_0 |
| 2 | 5x/3 | 0 | 2x/3 | Q_1,L |
| 3 | 19x/9 | 4x/9 | 4x/9 | Q_2,X_pre |

Immediately after event 3 the messenger moves left at -1/4 and X moves right at +2. The messenger reaches L at

    B=35x/9,

when the continuing fast X would be at 4x. Its prospective Y contact is at

    A=17x/9+y/2,

so A-B=(y-4x)/2. On both selected chambers, B<A. At B the messenger changes to speed +4. If X remained fast, the messenger would catch it at

    time 53x/9, position 8x.

Therefore y<8x makes the X/Y contact happen first; y>8x makes the Q_4/X_fast contact happen first. This comparison is used only after the already certified common prefix, rather than running a hypothetical trajectory through an earlier wrong collision.

### 2.3 The Z word, with 4x<y<8x

Put

    F=(10y-8x)/9.

The remaining table is

| Event | Time | Messenger position | X position | Contact |
|---|---:|---:|---:|---|
| 4 | 35x/9 | 0 | 4x | Q_3,L |
| 5 | 17x/9+y/2 | 2y-8x | y | X_fast,Y |
| 6 | 11x/3+5y/18 | F | F | Q_4,X_post |
| 7 | 25(2x+y)/18 | 0 | F | C_Z,L |

The seven flight durations, including the common prefix, are

    x, 2x/3, 4x/9, 16x/9,
    (y-4x)/2, 2(8x-y)/9, F.                  (4)

All are positive on P_Z. The return changes x to F and leaves D,y unchanged. Its determinant in (D,x,y) coordinates is -8/9, consistent with its odd length.

### 2.4 The N word, with y>8x

After common event 3, the remaining events are

| Event | Time | Messenger position | X position | Contact |
|---|---:|---:|---:|---|
| 4 | 35x/9 | 0 | 4x | Q_3,L |
| 5 | 53x/9 | 8x | 8x | Q_4,X_fast |
| 6 | 125x/9 | 0 | 8x | C_N,L |

The six flight durations are

    x, 2x/3, 4x/9, 16x/9, 2x, 8x.           (5)

This return changes x to 8x and leaves D,y unchanged. Its determinant is +8, consistent with its even length. No X/Y collision occurs on this word.

## 3. Complete chronology and exactness

Throughout either word, the spatial order is L,Q,X,Y,R, with only the indicated adjacent pair coincident at an event. This is an order of live strands rather than their labels. At common events 1,2,3, the positions x,2x/3,4x/9 are positive and strictly below y; at event 4, X=4x lies strictly between 0 and y.

For the Z word, at event 5,

    0<2y-8x<y,

because 4x<y<8x. At event 6,

    F>0,   y-F=(8x-y)/9>0.

At event 7, X=F is still between the anchors and Y. For N, 0<8x<y guarantees the final two configurations are ordered. R stays beyond Y in both branches.

Every adjacent gap is affine on each declared flight. A gap positive at both endpoints remains positive throughout. The departure gap has positive outgoing derivative, and the arrival gap has negative incoming derivative; all speeds are distinct for their collision partners. A gap zero at just one endpoint is therefore strictly positive in the flight interior. No nonadjacent pair can meet without an adjacent gap vanishing. Hence the endpoint tables and positive durations prove the complete chronology, including absence of unlisted or simultaneous remote contacts.

For an exact coefficient certificate, write in P_Z

    a=y-4x>0, b=8x-y>0, c=D-y>0,
    x=(a+b)/4, y=2a+b, D=2a+b+c.             (6)

For P_N, write

    a=x>0, b=y-8x>0, c=D-y>0,
    x=a, y=8a+b, D=8a+b+c.                  (7)

Every noncontact event gap and every duration becomes a nonzero nonnegative rational combination of a,b,c. The checker records these coefficients, not samples.

Conversely, for the Z word after the valid common prefix, event 4 before event 5 requires y>4x, while the X/Y contact before Q_4 catches X_fast requires y<8x. Initial ordering is also necessary. For the N word, the absence of the X/Y collision before the fast catch requires y>8x. The equalities give respectively the remote tie and triple collision just described. These are first-failure arguments, so no invalid prospective path is continued. Thus (3) gives the exact chambers for these selected complete words.

## 4. Physical inverse and nondestructive test

### 4.1 Why the section boundary matters

Simply negating all speeds at the outgoing section is not a legal phase switch. Instead the final forward anchor collision is used as the interface. Its incoming speed is -1, so it can emit the speed +1 reverse-entry messenger. The reverse run starts by undoing the *preceding non-anchor* event. At its other end, a fresh L collision sends the returning speed -1 messenger into the desired outgoing speed +1 control phase. All changes occur at actual binary contacts.

For each branch c in {Z,N}, make fresh reverse labels, denoted by bars with subscript c. The reverse label of a forward signal has the negative speed. Stationary base markers retain their original labels. A bar on C_c therefore has speed +1. Use the interface rule

    {C_c,L} -> {bar(C_c),L}.

The first reverse contacts are

    {bar(C_Z),X_0} -> {bar(Q_4)_Z,bar(X_post)_Z},
    {bar(C_N),X_0} -> {bar(Q_4)_N,bar(X_fast)_N}.

For Z add

    {bar(X_post)_Z,Y} -> {bar(X_fast)_Z,Y}.

For both c add

    {bar(Q_4)_c,L}                -> {bar(Q_3)_c,L},
    {bar(Q_3)_c,bar(X_fast)_c}    -> {bar(Q_2)_c,bar(X_pre)_c},
    {bar(Q_2)_c,L}                -> {bar(Q_1)_c,L},
    {bar(Q_1)_c,bar(X_pre)_c}     -> {bar(Q_0)_c,X_0},
    {bar(Q_0)_c,L}                -> {Q_out,c,L}.

Here Q_out,c has speed +1 and may be the next instruction's entry phase. The inverse marker-only rule changes no messenger label. Tagging every reverse phase by c preserves the branch even after the two reverse geometries enter the common setup portion.

### 4.2 Chronology and restored data

Let one forward branch have m events, duration T, and configurations at times

    0=t_0<t_1<...<t_m=T.

From the outgoing interface at time T, the reverse events occur after durations

    T-t_(m-1), T-t_(m-2), ..., T-t_1, T.

The first m-1 contacts have the same positions as forward events m-1,...,1, with every line's velocity negated. The last contact is at the original L position, and is the fresh terminal bounce above. There is no reverse of the forward final anchor event at zero elapsed time. There is no missing physical terminal contact.

Between contacts the complete five-strand configuration is the forward configuration at the reflected time. Therefore all strict separations and positive flight durations are preserved, and there are exactly m inverse events. Stationary labels restore at the end, X returns to x, Y returns to y, and D remains D. The only retained information is Q_out,Z versus Q_out,N.

This is an explicit inverse *gadget*, using new labels. It is not a claim that the globally completed original rule table is reversible. The branch-specific reverse rules are unambiguous because their inputs use fresh phase labels. All consume two signals and produce two signals at distinct speeds.

Thus the nondestructive test has 14 events on P_Z and 12 on P_N, and respective durations

    T_test,Z=25(2x+y)/9,
    T_test,N=250x/9.                            (8)

It is identity on all three homogeneous section coordinates. In particular it leaves no hidden moving marker, shifted anchor, unreset marker phase, or unrecorded scale factor.

## 5. Uniform separated counter encoding

For D>0 and a,b in N, use (1). Then

    D/20<x<=3D/20,
    17D/20<=y<19D/20.                          (9)

The closure of this encoding rectangle lies strictly inside the ordered section; its limiting points as a or b tends to infinity are ordinary interior shapes, not collisions.

If a=0, x=3D/20, so

    y-4x>=D/4,
    8x-y>D/4,
    x>=D/20,  D-y>D/20.                       (10)

Thus every zero-A encoded state belongs to P_Z. If a>0, x<=D/10, so

    y-8x>=D/20, x>D/20, D-y>D/20.             (11)

Thus every positive-A state belongs to P_N. The margin between zero and positive supports is uniform over the other counter. Both the secondary remote-tie surface y=4x and the primary branch surface y=8x have positive margins on all encoded states.

Even the intermediate changing-test outputs have uniform section gaps: on the Z encoding,

    y-F=(8x-y)/9>D/36;

on N, y-8x>=D/20. Hence the inverse construction does not conceal a limit where the marker section degenerates.

For B, reflect about R. Its nearest-target distance and spectator distance are

    r=D-y=D(1/20+(1/10)2^(-b)),
    s=D-x=D(19/20-(1/10)2^(-a)).              (12)

The identical test, with all physical speeds negated, tests b. Reflection changes no distance-coordinate inequality or duration. Reach R from the standard L section by crossing X, crossing Y, and bouncing at R; this takes three events and time D. After the test, return by crossing Y, crossing X, and bouncing at L; again three events and time D. Stationary labels and marker positions do not change in these transfers.

This establishes coverage for *all* encoded states directly. It does not infer a finite cover from local realizability and does not assign a separately compiled rule table to each counter value.

## 6. Uniform increment and positive decrement

Only two standard nearest-target operations are needed. Their proofs are included to make guard coverage explicit. They use a stationary anchor 0, a nearest target t, a stationary spectator s, a far reflector D, with 0<t<s<D. Reflection gives the right-anchor versions.

### 6.1 Four-event anchored scaling

For a fixed rational k>0, put

    h=(k-1)/(k+1), so -1<h<1.

The messenger starts at the anchor with speed +1. At t it launches the target at speed h and reverses at -1; at the anchor it reverses at +1; at the next target contact it restores the target and reverses at -1; at the anchor it reverses at +1 into the next phase. The four times and positions are

    (t,t), (2t,0), (2t+kt,kt), (2t+2kt,0).

The target equation t+h(t+kt)=kt holds exactly. Its segment is monotone from t to kt. The exact guard is

    0<t<s<D,   0<kt<s.                        (13)

These endpoint inequalities imply every flight is positive and no spectator contact occurs. Conversely an obstructed endpoint forces an adjacent-marker contact or collapsed/reordered flight no later than the supposed restoration. Duration is 2(1+k)t.

### 6.2 Ten-event translation

For rational e<1, the operation t -> t+eD has exact guard

    0<t<s<D,   0<t+eD<s.                      (14)

This is Report 63, §3, restated here. Put u=t/(1-e), h=e/(2-e). First perform a four-event scaling t -> u as above. Then launch the target at the same h as the messenger passes outward; cross the spectator, bounce at D, cross the spectator inward, restore the target at t+eD while continuing inward, and bounce at the anchor. Those last six messenger positions are

    u, s, D, s, t+eD, 0.

Their flight lengths are u,s-u,D-s,D-s,s-(t+eD),t+eD. The moving target's restoration equation is

    u+h[(2D-(t+eD))-u]=t+eD.

Moreover u lies between t and t+eD, since

    u-t=e t/(1-e),
    (t+eD)-u=e(D-(t+eD))/(1-e).

Thus (14) also guards the hidden intermediate scale, and the moving target remains strictly inside (0,s). Every spectator crossing is listed. The operation uses ten events, restores the full anchor section, and has duration

    2[t+t/(1-e)]+2D.                          (15)

Fresh temporary marker and messenger labels make both halves deterministic even when phase speeds agree. No upstream constructor is needed.

### 6.3 Application to the encoded bands

Let a target's encoded distance be

    t=D/20+(D/10)2^(-n).

An increment n -> n+1 is exactly

    t -> t/2 -> t/2+D/40.                     (16)

Use scaling k=1/2 and translation e=1/40. For every n>=0, t lies in (D/20,3D/20]; the first endpoint is at most 3D/40, and the final endpoint is in (D/20,D/10]. Every endpoint lies strictly below s>=17D/20, with positive distance from 0.

A positive decrement n -> n-1, used only after a positive test, is exactly

    t -> 2t -> 2t-D/20.                       (17)

Here n>=1 implies D/20<t<=D/10. The first endpoint is in (D/10,D/5] and the last in (D/20,3D/20]. Again every endpoint satisfies (13) and (14) uniformly. The hidden translation endpoint is between the stated endpoints, by §6.2. No operation on an inadmissible zero input is needed or claimed.

Each update uses 14 events, fixes the other counter, and returns to the same anchor section. The only moving-target speeds used are

    -1/3, +1/3, 1/79, -1/41

in distance coordinates. Applying the reflected versions updates B. For either update the duration is strictly between 2D and 4D. Explicitly, in terms of its original entering t, the increment duration is

    2D+(196/39)t,

and the positive-decrement duration is

    2D+(290/21)t.

The admitted t ranges above prove the claimed simple bounds.

## 7. One fixed finite rule table for a fixed counter program

Take the standard deterministic instruction set

    INC A; go to j,
    INC B; go to j,
    if A=0 go to j0, otherwise A:=A-1 and go to j1,
    if B=0 go to j0, otherwise B:=B-1 and go to j1,
    HALT.

An instruction section has the base four stationary marker labels and an outgoing speed +1 messenger Q_i identifying the current instruction. Make fresh copies of all intermediate phases for each instruction and each branch needing them. The finite copies do not add live signals. Each intended interface is implemented by choosing the outgoing messenger label at that block's existing terminal anchor collision.

- INC A: the 14-event update (16), with the final L bounce emitting Q_j
- INC B: transfer to R, reflected update (16), transfer back; 20 events
- Conditional A: nondestructive test, with zero's final reverse L bounce emitting Q_j0 and positive's final reverse L bounce emitting the decrement entry phase; the decrement's final L bounce emits Q_j1. This gives 14 events on zero, 12+14=26 on positive
- Conditional B: transfer to R, reflected test, decrement there on the positive branch, and transfer back with the appropriate control label. This gives 20 events on zero, 32 on positive

Every marker-only event uses an instruction-specific moving-marker label, so two instructions cannot accidentally share an ambiguous marker-only input rule. Inverse marker labels are also branch tagged. At no marker-only event is a remote messenger's phase changed. Each transfer includes all marker crossings, and no stationary marker is relabeled at a distant point.

All explicitly used collision inputs are distinct or have exactly the same intended output; in this construction fresh phase copies make them distinct whenever the contexts differ. Complete the finite table by identity rules on every otherwise unspecified finite label set with pairwise distinct speeds. Every such rule preserves cardinality. On the encoded executions these extra rules do not insert an unlisted event, because the complete chronology proofs have already excluded every extra meeting.

Exactly five signals therefore persist. The rule table and finite set of labels depend on the fixed finite program, but are independent of a,b and D. A common speed set for every compiled program is

    {0} union +/-{1, 1/3, 1/79, 1/41, 3/2, 1/4, 4, 1/2, 2},

which has 19 elements. This is an upper bound, not an optimality claim. Rational initial D yields rational initial positions and rational collision positions and times for every finite run.

Induction on the simulated instruction count proves correctness: (1) holds initially; §§5–6 implement the exact prescribed branch and counter operation; §7 restores the section with the correct next control label. The same finite rules therefore apply to every subsequent encoded state.

## 8. Timing, halting, and boundedness

From (8)–(11), every A test has duration strictly between D and 4D. The reflected B test with its two transfers has duration between 3D and 6D. Updates cost between 2D and 4D; transfers cost D apiece. Thus every nonhalting instruction transition takes strictly between D and 10D, with at most 32 binary events.

A halt means reaching a full section with a designated Q_H label. It need not mean that all physical motion stops. If a finite-collision halting convention is desired, assign Q_H speed +1 and use identity crossings with X,Y,R, so the messenger then leaves to the right and has no further collisions. There are exactly three subsequent crossings and still exactly five live signals. Alternatively a separately specified harmless bounce cycle can retain spatial confinement after halt, but then finite-collision halting is not the convention. Our principal simulation theorem uses designated-section reachability.

Before halt all positions remain in [0,D]: the test tables and their reversals do, each update's target remains between its anchor and spectator, and transfers stay in the interval. The scale D never changes. An infinite machine run has instruction-section times at least nD, so it has no finite-time accumulation. Inside any individual instruction there are finitely many strictly separated collisions; this rules out an accumulation hidden inside one transition as well. No continuation after an accumulation is invoked.

The encoding uses arbitrarily fine rational distances and exact collision rules. There is no robustness-to-noise claim, finite-precision hardware claim, minimum-speed claim, or lower bound on the population of other encodings. In particular the 19-speed count and 32-event bound are explicit convenient bounds, not optimization results.

## 9. Static arithmetic evidence

`static_algebra.py` is a new, standalone Python standard-library checker, displayed and inspected before execution. It contains the two tables as rational linear rows. It checks each endpoint difference against the prescribed velocity times the declared flight duration; computes every adjacent gap and duration in the chamber coordinates (6) and (7); checks exactly the designated gap vanishes at each event; and verifies the affine endpoint maps and inverse-by-time-reflection identities. It also checks the uniform encoding and update guards on the vertices of the relevant closed rectangles, and checks all update and test duration identities.

These are static row identities and linear-inequality certificates, not a physical simulator: the checker never asks which collision is next, evolves no signal configuration, imports no earlier implementation, and searches for no collision schedule. The proof of chronology is §§2–3; the output is supporting exact arithmetic. `evidence/static_checks.json` records the exact coefficients and checker hash. A manifest records hashes of this proof, the checker, the retained dependency, and evidence.

## 10. Primary-source positioning

1. J. Durand-Lose, *Abstract geometrical computation for black hole computation (extended abstract)*, MCU 2004 / LNCS 3354 (2005), §3, author-manuscript PDF pp.6–8, especially the counter encoding and Figs.2–5. It specifies two fixed scale signals, one signal per counter, and one instruction signal, and uses equal-cardinality rules. It already supplies the essential bounded-population counter-computation precedent. Its arrangement permits changing counter-marker order and places zero counters beyond the unit marker. Our fixed ordered section and guard tables are a different, explicitly certified interface, not a new discovery of five-signal universality.

   https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2004_MCU.pdf

2. J. Durand-Lose, *Reversible conservative rational abstract geometrical computation is Turing-universal*, CiE 2006, LNCS 3988, pp.163–172, §2.2, manuscript PDF p.5, explains time reversal by opposite speeds and reversed collision rules. The current reverse gadget uses this standard principle, with explicit care for its outgoing-section boundary and branch tags; it does not assert global reversibility after arbitrary identity completion. Its §5 and Fig.5 also reiterate the geometric counter encoding.

   https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2006_CiE.pdf

3. F. Becker et al., *Abstract Geometrical Computation 10: An Intrinsically Universal Family of Signal Machines*, definitions in §2, supplies the usual distinction between finite meta-signals, their fixed speeds, and individual live occurrences. Our five count is live occurrences; it is not five meta-signals.

   https://arxiv.org/abs/1804.09018

4. A. Dudenhefner, *Certified Decision Procedures for Two-Counter Machines*, FSCD 2022, §2 and Theorem 6, states the standard increment and conditional-decrement instruction model and undecidability, while emphasizing dependence on the exact instruction set. Our theorem is a direct compiler for the stated instruction semantics. Any fixed universal-program corollary requires that separate standard discrete universality fact; it is not proved by our collision algebra alone.

   https://doi.org/10.4230/LIPIcs.FSCD.2022.16

These sources were read as primary literature. No novelty, priority, or exhaustive-search claim is made. The technical addition to the immediately preceding local-realization packets is a globally guarded encoded computation with a real finite branching rule, rather than merely a map valid around one point.
