# Exact constant-duration instructions with five live signals

4 October 2026. A separate continuation of the frozen full-section compiler in `five-signal-branching64-20261004/PROOF.md`. The frozen proof and Report 64 manuscript are not edited. The construction below changes only the routing of a compiled core's terminal control label into a new identity-padding gadget, at that core's existing final contact. Its core trajectories, counter updates, and duration formulas are unchanged.

## 1. Result and scope

Use four stationary markers with literal labels `L,X_0,Y,R`, at

    L=0, X=x, Y=y, R=D, 0<x<y<D,

and one outgoing messenger at L with speed +1. The instruction and branch are encoded by its finite label. We use the frozen compiler's encoding

    x=D(1/20+(1/10)2^(-a)),
    y=D(19/20-(1/10)2^(-b)),       a,b in N, D>0.

**Clocked-compiler theorem.** For every fixed finite two-counter program using the frozen instruction set, a finite rational-speed signal machine simulates every initial encoded counter pair with exactly five live signals, restores this same ordered full section after each nonhalting instruction, and takes exactly `30D` per instruction. A common speed set of 39 rational numbers works for every compiled program. Each instruction has at most 54 binary collisions, counting every identity crossing. All phase changes occur at actual binary contacts. No extra clock signal, moving auxiliary marker, change of scale, or counter displacement is introduced by the padding.

The time is constant across instructions, branches, and counter values in each run. It scales with D; taking D=1 gives duration 30 in fixed time units. No optimality claim is made for 30, 54, or 39. The frozen core remains the dependency for its original instruction geometries and all encoded-state guards. The new identity gadget is independently proved on the entire ordered section, not merely on the encoded subset.

The result is a clocked refinement of an explicit interface. It is not a claim of first five-signal universality or a novel general bouncing-delay principle; see §9.

## 2. Core durations in the geometry available at padding entry

Let `(D,x',y')` be the *output* section coordinates of a completed core instruction. The padding sees these stationary positions, not the input coordinates. We write the core elapsed time as

    T_c=alpha_c D+beta_c x'+gamma_c y'.             (1)

The six triples, with exact original-core counts, are:

| Core branch c | alpha | beta | gamma | Core events |
|---|---:|---:|---:|---:|
| A increment | 341/195 | 392/39 | 0 | 14 |
| A conditional, zero | 0 | 50/9 | 25/9 | 14 |
| A conditional, positive decrement | 383/126 | 1310/63 | 0 | 26 |
| B increment | 69/5 | 0 | -392/39 | 20 |
| B conditional, zero | 31/3 | -25/9 | -50/9 | 20 |
| B conditional, positive decrement | 155/6 | 0 | -1310/63 | 32 |

Here `69/5=897/65` and `155/6=1085/42`; the unreduced forms also agree with the proposed triples.

### 2.1 Independent derivation

In nearest-target coordinates t, an update consists of a scaling followed by a translation. Their frozen formulas give

    T_inc(t)=3t + 2[t/2+(t/2)/(1-1/40)]+2D
            =2D+(196/39)t,

    T_dec(t)=6t + 2[2t+(2t)/(1+1/20)]+2D
            =2D+(290/21)t.

The nondestructive positive test takes `(250/9)t`. Therefore its followed-by-decrement core takes

    T_pos(t)=2D+(2620/63)t.                       (2)

For an A increment, `x'=t/2+D/40`, so `t=2x'-D/20`. Substitution in `T_inc` gives `341D/195+(392/39)x'`. For an A positive decrement, `x'=2t-D/20`, so `t=x'/2+D/40`. Substitution in (2) gives `383D/126+(1310/63)x'`.

On an A zero branch the test is nondestructive, and its elapsed time is `25(2x'+y')/9`.

For B, let r be the original distance from R to the B target. The two transfers add `2D`. A B increment has

    r=2(D-y')-D/20=39D/20-2y',
    T=4D+(196/39)r=(69/5)D-(392/39)y'.

A B positive decrement has

    r=(D-y')/2+D/40=21D/40-y'/2,
    T=4D+(2620/63)r=(155/6)D-(1310/63)y'.

Finally the B zero test uses target distance `D-y'` and spectator distance `D-x'`; hence

    T=2D+(25/9)[2(D-y')+(D-x')]
     =(31/3)D-(25/9)x'-(50/9)y'.

These are identities on each core branch's admitted domain. No claim is made that an inadmissible branch should execute on every ordered section.

## 3. Stationary identity shuttles, with all collisions counted

For this section drop primes and write the stationary padding coordinates as `(D,x,y)`. All speed magnitudes v below are fixed positive rational constants attached to labels. A shuttle over distance d at speeds +v and -v has elapsed time `2d/v`. Every marker remains stationary with exactly its original label. A crossing that changes no label is still a binary collision and is counted.

Let

    a=x>0, b=y-x>0, c=D-y>0.

The following are complete contact words, excluding the departure section contact and including the terminal contact. The corresponding flight lengths are listed in the same order. Every flight has duration its displayed length divided by v.

| Primitive | Contact word | Flight lengths | Duration | Events |
|---|---|---|---:|---:|
| L-X-L | X,L | a,a | 2x/v | 2 |
| L-Y-L | X,Y,X,L | a,b,b,a | 2y/v | 4 |
| R-X-R | Y,X,Y,R | c,b,b,c | 2(D-x)/v | 4 |
| R-Y-R | Y,R | c,c | 2(D-y)/v | 2 |
| L-R | X,Y,R | a,b,c | D/v | 3 |
| R-L | Y,X,L | c,b,a | D/v | 3 |
| L-R-L | X,Y,R,Y,X,L | a,b,c,c,b,a | 2D/v | 6 |

For the right-anchored loops, the outward speed is -v and the return speed +v. For a full-span L loop, the two crossings in each direction are spectator contacts, and both endpoint bounces are counted.

### 3.1 Full local rule schema

For every *occurrence* of a primitive in the compiler, use fresh messenger phase labels, including an instruction/branch tag. All stationary markers use the same base labels `L,X_0,Y,R`. Denote by S the chosen starting anchor, T the target, and B any stationary marker strictly between S and T.

An anchored round trip has an outward label `p_out` of speed `epsilon v`, where epsilon is +1 from L and -1 from R, and an inward label `p_in` of speed `-epsilon v`. Its complete nontrivial rules are

    {p_out,T} -> {p_in,T},
    {p_in,S}  -> {q_next,S}.                    (3)

At each intervening marker B install the two identity crossing rules

    {p_out,B} -> {p_out,B},
    {p_in,B}  -> {p_in,B}.                      (4)

The label `q_next` is the entry label of the next primitive, with its already specified rational speed, or the next instruction label at the final contact. For a full L-R-L loop, take S=L, T=R and both intervening markers X,Y.

For a one-way transfer use a fresh label `p_tr` at speed +1 from L to R or -1 from R to L. At both intervening markers use

    {p_tr,B} -> {p_tr,B},

and at the destination anchor T use

    {p_tr,T} -> {q_next,T}.                     (5)

There is no rule application at a departure point in these descriptions: the preceding primitive's terminal contact has already emitted the departure label. Equations (3)-(5) are thus a full local realization schema, not an instruction to change speed remotely.

All rule inputs contain the moving messenger and one stationary marker. Their two incoming speeds are distinct, and their two outgoing speeds are distinct because every listed messenger speed is nonzero. Labels used in different primitive occurrences are fresh, so no input pair has two outputs. Identity completion for unused finite distinct-speed inputs can be made exactly as in the frozen compiler. Number preservation is immediate.

### 3.2 All-parameter chronology

Every listed length is one of a,b,c, hence positive. Between two listed contacts the messenger moves monotonically through one open interval between consecutive stationary markers. There is no other marker in that interval. At a crossing it continues in the same direction; at a target bounce it reverses direction; at a terminal anchor it departs into the interval. Thus the next listed contact is necessarily the next physical contact. The three other stationary positions are distinct from the contacted one. Since stationary markers never move and there is just one moving signal, neither a remote simultaneous collision nor a triple collision is possible.

At a contact with L the distances to the other markers are `a,a+b,a+b+c`; with X they are `a,b,b+c`; with Y they are `a+b,b,c`; with R they are `a+b+c,b+c,c`. All are strictly positive. This explicitly covers every possible padding contact.

Consequently the exact common guard is the entire ordered full section `0<x<y<D`. Conversely its boundary causes coincident stationary markers or a zero flight in the mandatory full-span loop, so it is excluded by the strict binary-section convention. Each primitive fixes D,x,y and all four marker labels. No hidden temporary marker survives because none is introduced.

## 4. A general homogeneous clock-padding lemma

**Lemma.** Suppose a finite collection of already implemented cores returns to the ordered full section with an outgoing +1 messenger at L, and on branch c has rational elapsed-time expression (1) in its output coordinates. Let C be a positive rational constant satisfying, for every branch,

    C > 4+alpha_c+max(beta_c,0)+max(gamma_c,0).  (6)

Then each core can be followed by a five-live-signal identity gadget so that the combined duration is exactly CD. The gadget uses at most 26 collisions. Its speeds and labels are finite for any finite family of cores and are independent of the section coordinates.

**Proof.** Fix c, drop its subscript, and put

    l_X=max(-beta,0),  r_X=max(beta,0),
    l_Y=max(-gamma,0), r_Y=max(gamma,0),
    k=C-alpha-r_X-r_Y-4 > 0.                   (7)

The desired padding time has the positive-distance decomposition

    CD-T = (4+k)D
           +l_X x+l_Y y+r_X(D-x)+r_Y(D-y).      (8)

Indeed the D coefficient is `4+k+r_X+r_Y=C-alpha`, while the x and y coefficients are `l_X-r_X=-beta` and `l_Y-r_Y=-gamma`. Thus a negative desired coefficient is represented by the distance to the opposite anchor and an adjusted fixed D term; there is no negative waiting interval.

Execute this physically ordered sequence:

1. Start with a full L-R-L loop at speed magnitudes 1, taking `2D` and six events. Its last L collision selects the entry speed of the next primitive.
2. If `l_X>0`, execute L-X-L at magnitude `2/l_X`. If `l_Y>0`, execute L-Y-L at magnitude `2/l_Y`. Their durations are `l_X x` and `l_Y y`. A missing loop is omitted by choosing the next actual departure label at the previous actual terminal collision.
3. Transfer L-R at +1, taking D and three events. At R emit the first right-loop label, or the return-transfer label if no right loop is needed.
4. If `r_Y>0`, execute R-Y-R at magnitude `2/r_Y`. If `r_X>0`, execute R-X-R at magnitude `2/r_X`. Their durations are `r_Y(D-y)` and `r_X(D-x)`.
5. Transfer R-L at -1, taking D and three events. Its L arrival emits the final-loop label at speed `2/k`.
6. Execute a full L-R-L loop at magnitude `2/k`, taking kD and six events. Its final L collision emits the next instruction's +1 entry label.

The initial full-span loop is important: the inherited padding-entry speed is +1. The construction does not silently replace that outgoing speed by `2/l_X`, `2/l_Y`, or `2/k`. The first selection of a new magnitude is at the fresh final L contact of step 1. All later selections are at the anchor contacts described in (3)-(5). No free phase switch or zero-time extra collision is used anywhere.

Steps 1,3,5 cost `4D` and 12 events. Step 6 adds kD and six events. For each coordinate exactly one of its left or right coefficients can be nonzero, so there are at most two target loops, each using at most four events. This yields at most `12+6+8=26` padding events. Their time sum is (8). The proof in §3 applies on every ordered output section and composes because each final contact has exactly the outgoing phase needed by the next positive-length flight. All marker labels and positions are fixed throughout. This proves the lemma.

For an arbitrary finite homogeneous family, one can always choose a rational C satisfying (6). This is a sufficient construction, not a best possible threshold. If the same finite template family is used for all source programs, its enlarged speed set is common to all those programs; only finitely many phase copies depend on the program.

## 5. The six explicit 30D padding words

Apply the lemma with C=30. The following table gives all nonzero target loops. In a notation such as `RX(q)`, q is the duration coefficient, so the loop has time `q(D-x')` and speed magnitude `2/q`. `LX(q)`, `LY(q)`, and `RY(q)` have times `qx'`, `qy'`, and `q(D-y')`. All primed coordinates remain fixed throughout padding.

| Branch | Left loops, in order | Right loops, in order | k | Final-loop magnitude 2/k |
|---|---|---|---:|---:|
| A increment | none | RX(392/39) | 71/5 | 10/71 |
| A zero | none | RY(25/9), RX(50/9) | 53/3 | 6/53 |
| A positive | none | RX(1310/63) | 13/6 | 12/13 |
| B increment | LY(392/39) | none | 61/5 | 10/61 |
| B zero | LX(25/9), LY(50/9) | none | 47/3 | 6/47 |
| B positive | LY(1310/63) | none | 1/6 | 12 |

Each row includes the mandatory unit-speed initial full loop, both unit-speed transfers, and its final full loop, even when the target loops all lie on one side. The four possible target-loop magnitudes are

    coefficient 392/39 -> speed 39/196,
    coefficient 25/9   -> speed 18/25,
    coefficient 50/9   -> speed 9/25,
    coefficient 1310/63 -> speed 63/655.

Every k is positive. The smallest is `1/6`, on B positive. This proves that the proposed C=30 suffices without relying merely on the coarser frozen estimate `T<10D`.

### 5.1 Event ledger

| Branch | Core events | Target-loop events | Fixed padding events | Total padding | Combined events |
|---|---:|---:|---:|---:|---:|
| A increment | 14 | 4 | 18 | 22 | 36 |
| A zero | 14 | 2+4 | 18 | 24 | 38 |
| A positive | 26 | 4 | 18 | 22 | 48 |
| B increment | 20 | 4 | 18 | 22 | 42 |
| B zero | 20 | 2+4 | 18 | 24 | 44 |
| B positive | 32 | 4 | 18 | 22 | 54 |

The coarse generic estimate `32+26=58` is valid. The actual six templates give the stronger bound 54. This is simply exact accounting for this construction, not an optimization theorem. No interface event is double-counted: the core's final L collision belongs to the core, while padding first contacts X after a positive flight. Within padding, a preceding primitive's terminal contact is counted once and emits the next departure label; the next primitive counts only subsequent contacts.

### 5.2 Fixed speed ledger

A sufficient core speed set is the frozen set

    {0} union +/-{1,1/3,1/79,1/41,3/2,1/4,4,1/2,2}.

Add

    +/-{39/196,18/25,9/25,63/655,
        10/71,6/53,12/13,10/61,6/47,12}.       (9)

These ten positive magnitudes are pairwise distinct and distinct from the nine core magnitudes. The enlarged set therefore has `1+2(9+10)=39` speeds. A phase label retains its fixed speed everywhere; a speed changes only by replacing that label at a listed collision. The choice of speed set depends on neither a,b,D nor the finite source program. It is the number of labels and rules, not the set of speed values, that grows with the source program.

## 6. Compiling the interfaces, branch memory, and exact state preservation

For each source instruction i and each realized branch c, take a fresh copy of the padding labels in §§3-5. Retarget the core's existing last L rule so that it emits that branch's fresh padding-entry label at the same speed +1 formerly used for the next instruction. The output stationary label stays L. There is no alteration of any core flight, time, other collision, or counter output.

For conditionals, the core's zero and positive outputs already have branch-specific finite control labels. These select different fixed padding copies; no measurement of elapsed time or remote decision is required. The chosen next instruction j is carried in those finite labels. It is emitted only by the final L bounce of that copy's final full-span loop.

Every padding rule leaves every marker at exactly its incoming position with its literal base label. The entire full section after padding is therefore

    L=0, X=x', Y=y', R=D, messenger at L outgoing +1 with label Q_j.

The values x',y' are precisely the original core's computed counter encoding. The padding does not re-encode, renormalize, approximate, or apply an inverse update. No data is stored in an extra signal, shifted anchor, or altered stationary label.

Fresh instruction/branch/stage labels make the rule table finite and deterministic for a fixed finite program. Each new rule consumes two signals and creates two, and identity completion preserves this property for unused distinct-speed inputs. Encoded executions use only the proved binary words. Thus the total population is exactly five, including the two outgoing strands at a contact.

## 7. Iteration, halting, and nonaccumulation

The frozen core's uniform encoded-state guards hold before every core by induction. Each core restores its required ordered output section; §3 then gives the padding guard automatically. The padding restores the identical coordinates and the correct next instruction label. Therefore the same compiled finite table executes all subsequent instructions for all initial counter pairs.

If the initial instruction section is at time 0, the n-th completed nonhalting instruction section is exactly at

    t_n=30nD.

All positions remain in `[0,D]` until reaching a halt section. There are at most 54 strictly time-separated collisions in any one instruction. Hence an infinite computation has no finite-time collision accumulation, and no continuation through an accumulation is invoked.

The clock applies to transitions of nonhalting instructions. A halt is the designated full-section label `Q_H`, as in the frozen theorem. The optional convention allowing Q_H to escape through three later identity crossings can be retained; those are post-halt events, not another simulated nonhalting transition.

The construction is exact. It makes no robustness, finite-precision, minimum-population, global-reversibility, or optimal-speed claim.

## 8. Fresh static arithmetic evidence and preservation

`static_clock_algebra.py` is newly written standard-library Python. It was displayed and inspected before execution. It uses exact `Fraction` rows to:

- derive both update costs from their scaling-plus-translation formulas;
- derive all six output-coordinate duration triples, checking the inverse input/output substitutions;
- verify all declared primitive flight-length sums and all positive-gap contact separations;
- compute each positive k, every loop speed, and the complete exact identity `T_c+P_c=30D`;
- count every contact in the declared words and verify the exact maximum 54;
- verify that the ten added positive speed magnitudes are new, giving 39 speeds in total;
- check the frozen core proof's SHA-256 digest without writing to that dependency.

It is a static row certificate, not a physical simulator: it does not select the next collision, evolve a physical configuration, search for schedules, load a saved event schedule, import or execute prior scientific code, run author/upstream software, or invoke a proof assistant. The chronology proof is §3, and the physical interface proof is §4; exact arithmetic supports rather than replaces them.

`evidence/static_clock_checks.json` records the results, primitive rows, branch ledger, speed set, and checker hash. `evidence/checker.stdout.json` is the retained output. The frozen dependency digest is

    85f5de45c0a30f8bdf45b82a613ef9e5a8c766b5d8215d17a3ebbbd0f60b370f.

This packet is separate from Report 64 and does not modify its scientific core or manuscript.

## 9. Primary-source positioning and limits of precedence checking

1. **J. Durand-Lose, MCU 2004 / LNCS 3354 (2005), §3, manuscript pp.6-8.** This already uses two fixed scale signals, two counter-position signals, and one instruction signal with number-preserving rules. Its five-live-signal counter simulation is substantive prior art. The present theorem refines the later frozen fixed-ordered-section compiler; it does not newly establish five-signal universality. [Author manuscript](https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2004_MCU.pdf)

2. **J. Durand-Lose and A. Emmanuel, Abstract Geometrical Computation 11: Slanted Firing Squad Synchronisation on Signal Machines (2021), §§3-5, especially §4, manuscript p.8.** The paper explicitly implements delays by a signal going to a border and back, with speeds selected to obtain a desired multiple of the bounds' width. Its explicit bounce and delay rules are precedents for the basic geometric waiting mechanism. Its wider construction concerns recursively generated synchronization/accumulation structures, not this stated six-template five-live-signal clocked interface. [Primary preprint](https://arxiv.org/abs/2106.11176), [PDF](https://arxiv.org/pdf/2106.11176)

3. **J. Durand-Lose, Reversible conservative rational abstract geometrical computation is Turing-universal, CiE 2006, §2.2, manuscript p.5.** Opposite speeds and reversed rules are standard time-reversal tools underlying the frozen nondestructive test. This continuation neither needs a new reversal argument nor claims the completed compiled machine is globally reversible. [Author manuscript](https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2006_CiE.pdf)

These sources were read as primary literature. The limited check supports the stated caution about known population, reversal, and delay mechanisms. It does not establish absence of an earlier equivalent exact-clock compiler. No firstness, priority, exhaustive-search, or optimality claim is made.
