# Three-mass transitions through an existing unbounded residue-history packet

This is a concrete fixed-source route, not a new numerical universal bound. The existing `residue_affine_packed_history.py` already represents arbitrarily long trajectories of every fixed total positive residue-affine map. A fixed deterministic three-mass source has precisely such a map after a finite rejecting totalization. Its raw loader is affine. The physical clock needs an additional paid bridge; the prototype supplies one using the existing selected quotient fields and a squared-height radix. No external horizon occurs in the resulting source.

The prototype `three_mass_unbounded_interface.py` and receipt authenticate the existing arithmetic and residue-history sources. Four complete raw-SOS circuits are emitted, including all 16 native comparisons, both original outer comparisons, the output and clock constraints, affine input/output loaders, all coordinate unhattings and the final SOS. They are illustrative nonuniversal fixed machines. This new clock bridge has the proof below and bounded checks; it has not yet received independent review. No gigantic positive native Pell tuple is materialized. This is not a general public hostile-packet API.

## 1. Literal local source and a finite total map

The pinned three-mass core is `certificate.py`, SHA-256 `fed96578694af665258fca9eeab14fa94d8a56e810de8f684a2c9fdcd9d751e8`, from commit `4e270aa4648c5fd7e18626507531046715976535`. Its actual `branch_forms` at lines95–107, after `v=e+u` and on a selected branch, is:

|Kind at p=2 or3|Current N|Following N'|Native physical ticks|
|---|---|---|---|
|inc|v|pv|(108+96p)v+8|
|dec|pv|v|(96p+108)v+8|
|positive|pv|pv|192pv+8|
|zero, 1≤r<p|pv+r−p|same|192(pv+r−p)+8|
|nop|v|v|192v+8|

Selected v is a positive integer on complete natural zeros. On a zero branch set w=v−1, rho=r−1 and sigma=p−1−r. This is exactly the sparse I/D/T/Z local graph in `residue_affine_sparse_universal.md` §3. For I/D/T, w=v−1 and rho=sigma=0. The unbounded construction does **not** preserve the finite-horizon mass coordinates individually: it re-encodes the configuration history using the existing residue quotient words and native witnesses.

Assign original states distinct codes in 1,...,s, add a rejecting trap with code s+1, and choose K≥s+1 coprime to6. Encode the configuration by

    n=K(N−1)+q,        N≥1, 1≤q≤K.

The map follows each legal original transition. A missing guard, the halt state, the trap and unused labels go to the trap with unchanged N. The trap never exits. Thus reaching the original halt code at the end of a nonempty orbit occurs exactly at the first original halt. This totalization is important for preserving the exact clock: permitting arbitrary outgoing halt continuations would change that relation.

Put m=6K. For n=mz+r, 1≤r≤m, the residue fixes q, the payload modulo6 and hence its unique branch. Adding m increases payload by6. Consequently

    f(mz+r)=a_r z+d_r,       d_r=f(r)>0,

with a_r=mp, m/p or m for increment, decrement or an unchanged-payload branch. These are nonnegative integer slopes, so the existing complete residue-history theorem applies literally. There is no need to enumerate an unbounded state space; the fixed table has m rows. K coprime to6 is convenient and also matches the scalar factored-guard construction, although direct residue enumeration itself only needs m divisible by K,2,3.

For a fixed start code q0 and natural raw x, N0=x+1 gives the **two-gate** input port `K*x+q0`. A positive final payload F gives the three-gate target port `K*(F−1)+qhalt`. To retain the original natural output y, rather than silently changing its domain, the prototype supplies positive F and adds the comparison F=y. This explicitly rules out y=0. Merely feeding a possibly nonpositive encoded target to the positive-native theorem would not suffice.

The prototype handles q0≠halt and hence nonempty runs. If q0=halt, the original first-halting relation is just y=x+1 and T=0; it should be emitted as that separate small affine SOS, not by accepting arbitrary posthalt paths.

## 2. What the current sparse and FRACTRAN APIs do and do not supply

The complete sparse universal compiler imports an actual fixed U21 table and supports I,D,T instructions. Any specified three-mass source can be translated into those opcodes:

- inc becomes I;
- a positive-only decrement becomes D with its missing zero case sent to the trap;
- a pure positive or zero instruction becomes T with the missing case trapped;
- complementary positive/zero instructions at one source state combine into one T;
- nop becomes T with both targets equal (at any fixed supported prime).

The existing builder has at least three register-prime slots and requires slots1,2 to be primes3,2. Thus source counter0 maps to register2 and counter1 to register1; an unused prime5 can occupy slot0. Relabel the start instruction to0, give the trap an internal index, and use the table's unique terminal index for halt. This translation does not need source reversibility. It preserves raw payload steps, although nop and missing-guard normalization affect the fixed branch table and its paid size.

However, `residue_affine_sparse_universal.py::branches` always prepends two doubling-loader edges. Its complete theorem starts the body at E*2^x, for positive x; it is not a drop-in raw `x+1` compiler. Its paid ordinary-input theorem applies to its actual U21 strong interface with E=3^e. A new raw adapter would have to delete/replace and reprove that outer interface. The direct expanded residue-history route above instead consumes the raw affine input immediately.

The bounded `fractran_divisibility_residual_projection` retains an externally fixed horizon and does not supply an unbounded alternative. No fixed-arity unbounded FRACTRAN compiler was identified in that reviewed WIP route. The existing native/Pell theorem is useful through the already complete residue-history construction; a scalar FRACTRAN or counter-step graph alone does not pay chronology.

## 3. Exact clock without new native selection lanes

The physical tick value is affine on each of the same residue rows:

    tau(mz+r)=c_r z+b_r.

For increment, decrement and unchanged-payload branches respectively,

    c_r=6(108+96p),  6(96+108/p),  1152,
    b_r=tau(r).

These are exact integers. Crucially c_r depends only on the numerical slope a_r: the five possible ratios are 2,3,1/2,1/3,1. All no-motion tests and nops have the same clock coefficient. Give the artificial rejecting transitions the same unchanged-payload clock; their values do not affect an accepted orbit. Therefore the **already supplied** selected quotient words Z_a suffice. With baseline slope a0 and its clock coefficient c0, define the paid word

    Ctau=c0*W + sum_a(c_a−c0)*Z_a + sum_r b_r*E_r.

After the existing selector/range typing this is the sum of actual tick digits in the common time radix B. Every multiplication by a fixed nonunit coefficient and every sum is emitted; this word is not a free affine port.

A bare congruence does not establish a sum of arbitrarily many ticks. The proposed source replaces the old linear radix by

    h=n_initial+n_target+T+eta,     B=C*h²,

where eta>0, T is the original natural requested clock, and C is a fixed dyadic integer at least both the old radix multiplier and 2384m+2. The added height input and the height square are charged.

All old pretyping bounds remain valid since B dominates the old multiplier times h. In particular the global bound gives J≥1 and bounds the packed fields; the original complete native AND applies before digit assumptions. It forces B and P dyadic. Because B=C*h² and C is dyadic, integer h is dyadic as well. Thus the original range mask `(h−1)J` has the same exact meaning, and P=B^t with a nonempty, existentially decoded duration t. The old transport equation now proves the exact deterministic first-halt orbit.

Each current numerical value is in [1,mh]. No such value can repeat before the terminal halt: determinism would force a cycle, whereas the terminal halt is subsequently reached and its only successor is the permanently rejecting trap. Hence

    t≤mh.

The corresponding original payload is at most6h. Every real source step has

    0<tau≤396*(6h)+8≤2384h.

Consequently its ordinary sum is at most2384m h² and strictly below B−1. Also 0≤T<h<B−1. Supply one positive clock quotient hat and impose

    Ctau=(B−1)*(clock_quotient_hat−1)+T.

Reducing modulo B−1 now proves the requested T equals the actual clock, because both are in [0,B−2]. This is a genuine no-wrap argument derived from the already decoded halting chronology, not an assumption that an unbounded number of digits has small sum. Conversely, any real first-halting run can choose dyadic h large enough for its endpoints, actual clock and all residue quotients. The clock quotient is natural because `Ctau−sum(tau)` is a nonnegative multiple of B−1. All existing global-slack and native-extension completeness arguments survive the larger radix.

This gives the exact three-coordinate relation `(x,y,T)` for each specified nonempty-start source, with fixed scalar arity independent of runtime. It does not preserve the finite-horizon certificate's unique witness tuple: the height and native representations introduce their usual existential multiplicities.

For a clock scaled by4, scale every tick coefficient by4 and correspondingly enlarge the safe fixed radix multiplier. For the compact cleaned physical time the literal original formula is

    Tclean=2*Tnative+192*(x+1)+192*F+16.

It can be attached to this unbounded forward relation using a positive native-clock witness and a paid endpoint comparison. Given existing x,F,Tnative ports, computing this formula costs a literal2M+4A (`192*(F+x+1)+2*Tnative+16`); an additional SOS equality costs1M+2A and one finalizer addition already included in that latter count. This is an incremental schedule only; the prototype emits the native-time relation and does not claim a complete cleaned-time total. The full cleaned trajectory follows the previously proved unique reverse lift on actual forward histories.

## 4. Actual emitted evidence and scope

The raw parent has m+g+25 positive auxiliaries; the prototype adds positive F and the clock quotient, giving m+g+27, and has20 comparisons (16 native,2 inherited outer,2 new). It keeps natural external x,y,T. Literal full circuits, with all gates live, are recorded in the receipt:

|Fixed nonuniversal source|Full M|Full A|Total|Positive witnesses|Propagated degree upper bound|
|---|---:|---:|---:|---:|---:|
|INC2;DEC2|237|361|598|59|2344|
|prime-three zero test|182|291|473|57|1192|
|nop|180|291|471|57|1192|
|prime-three positive test|187|287|474|57|1192|

These costs are for unbounded histories, whereas the earlier44/43 examples fix horizon2; the different contracts prevent a direct improvement comparison. The complete source includes no existential external horizon and performs no exponentiation at runtime. The polynomial degree claims are only upper bounds, including the changed squared height.

The checker independently evaluates3000 numerical residue/clock identities,144 literal original branch/tick forms,72 complete accepted outer histories with the actual packed AND and all four outer comparisons,48 complete signed SOS evaluations and48 explicit height-interface identities. All four gate lists are independently recounted and checked closed/live. These checks do not supply huge native Pell witnesses or replace the general proof. The clocks are verified against the literal source interpreter, not against a free or guessed number of source steps. Original author suites are not rerun.

The standalone CLI uses authenticated source bytes rather than `.pyc`, records all executed local dependency hashes, and rejects `-O` because historical modules use assertions. The initial four source pins are checked before imports; deterministic receipt replay also compares the recorded dependency hashes. Run with repository verification dependencies, including SymPy:

    /path/to/research-venv/bin/python three_mass_unbounded_interface.py \
      --repo /path/to/Proofs --expect three_mass_unbounded_interface.json

## 5. Ordinary universal input is still a separate obligation

With final value and clock existentially hidden, every raw source halting language depends only on `(nu_2(x+1),nu_3(x+1))`. Multiplying the raw payload by an integer coprime to6 preserves all guards and the sequence of control states; every payload and the nonconstant tick contribution scale accordingly. Thus all source machines treat raw x=0 and x=4 identically for halting. This gives a concrete obstruction to calling raw `x+1` an arbitrary-r.e.-set universal ordinary-input interface.

The already paid U21 prefix avoids this obstruction by mapping ordinary positive x to E*2^x inside its chronology, with the represented set's fixed E=3^e. For a *specified* three-mass source with an appropriate strong two-counter program/input contract, counter relabeling plus an analogous prefix could be used. But neither three-mass archive delivers a numerical fixed universal separated reversible table or proves a simple ordinary `(e,x)` loader contract for it; the reviewed Morita existence/simulation theorem allows an effective source encoding. One must not silently replace that encoding by the U21 recipe. In particular, U21 has eight counters, while the three-mass source uses only two.

The concrete progress is therefore a paid unbounded **fixed-source raw reachability-and-clock construction**, and an exact map to existing sparse local graphs. Remaining universal work is the actual fixed source table, its ordinary-input/program recipe or explicitly compiled decoder, the chosen prefix's full emitted cost, and then the full numerical source audit. No new universal operation bound, optimality claim, or improvement on87 follows from this scout.
