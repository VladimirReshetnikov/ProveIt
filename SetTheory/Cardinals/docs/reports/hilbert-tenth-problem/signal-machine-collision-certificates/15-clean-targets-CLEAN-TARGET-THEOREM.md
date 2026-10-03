# Exact finite-configuration reachability with three conserved mass units

## Status and relation to the frozen construction

This is a separate compiler-composition extension of the three-mass construction. It changes no files in the frozen report9 release. It uses exactly that local-rule generator, instantiated on a new source machine whose logical computation runs forward and then uncomputes. The resulting fixed CA generally has different control types and local rules from the CA compiled from the original source.

The upper-bound model is a one-dimensional finite-alphabet reversible CA. A cell state is a finite subset of Boolean channel types; its conserved weight is the subset cardinality. Vacuum is the unique zero-weight state. All inputs and targets below have total mass exactly three. This is not the ordinary integer-state NCCA model where each integer state itself is its mass.

## 1. The fresh-start source transform

Let R have state set Q, initial state q0, final state qh, and J separated instructions. Operations are INC, positive-only DEC, NOP, ZERO, and POSITIVE, with tests leaving the counter unchanged. Multiple instructions on either side of a state are allowed only as disjoint ZERO/POSITIVE tests on the same counter. Assume:

1. No instruction has target q0
2. No instruction has source qh

The original source may get stuck at a nonfinal configuration. These assumptions are structural, independent of the particular counter input.

Construct R-clean with states F:q and B:q for q in Q, together with a new final state H. Its initial state is F:q0. For each instruction q --op--> q', include:

- F:q --op--> F:q'
- B:q' --op-inverse--> B:q

Here INC and DEC are interchanged, while ZERO, POSITIVE, and NOP are unchanged. Finally add:

- F:qh --NOP--> B:qh
- B:q0 --NOP--> H

H, not either copy of qh, is the sole designated final state supplied to the CA compiler.

### Lemma 1: reversible separated syntax

The forward copy preserves R's outgoing and incoming groups. In the backward copy, an outgoing group is an original incoming group with reversed operations, and an incoming group is an original outgoing group with reversed operations. A singleton arithmetic instruction remains a singleton. A group of tests remains the same disjoint pair on the same counter. Thus both syntactic conditions are preserved.

The first bridge occupies the empty outgoing side of F:qh and the empty incoming side of B:qh; both are empty because qh originally had no outgoing instructions. The second occupies the empty outgoing side of B:q0 because q0 originally had no incoming instructions, and the fresh incoming side of H. Every affected group is therefore a legal singleton NOP. H has no outgoing instruction.

### Lemma 2: exact restoration and first halt

For positive raw N write N=2^a 3^b c with gcd(c,6)=1. R interprets a and b as its two counters, and preserves c. If its run first reaches qh after h instructions, write the trace as

(q0,N0), (q1,N1), ..., (qh,Nh).

The run of R-clean is exactly

(F:q0,N0), ..., (F:qh,Nh),
(B:qh,Nh), (B:q_(h-1),N_(h-1)), ..., (B:q0,N0), (H,N0).

Each reverse arithmetic instruction is enabled at the actual forward output and restores the original raw integer. Each reverse test checks the same unchanged integer. Reversibility of R makes each backward step unique. Moreover q0 cannot occur at a positive source time because no instruction enters it, so B:q0 is not encountered prematurely. Hence H is first reached after exactly 2h+2 source instructions, restoring both counters and the entire cofactor c. This includes h=0, when q0=qh is necessarily isolated and the cleaned run consists of the two NOP bridges.

If R never reaches qh, its forward copy never takes the first bridge and cannot reach any B state or H. If R gets stuck nonfinally, so does its forward copy. Thus R-clean reaches H if and only if R halts.

### Why freshness cannot simply be dropped

The reversible separated source

q0 --ZERO counter-a--> q1,
q1 --INC counter-a--> q0,
q0 --POSITIVE counter-a--> qh

has an incoming instruction at q0. From raw N0=1, its forward trace is (q0,1), (q1,1), (q0,2), (qh,2). A naive backward copy first reaches B:q0 at N=2, before undoing the increment. A NOP exit there returns the wrong input; it also conflicts with the outgoing reverse DEC. The implementation rejects this source. Simply prepending a fresh NOP to an arbitrary reversible source can likewise conflict with existing incoming instructions and is not a valid general freshening argument.

## 2. Exact whole-configuration reachability

Apply the existing three-mass compiler to R-clean. Denote the resulting native CA by A. Its canonical configuration C(q,N) has the fixed right-marker channel at coordinate 0 and the clean stage-zero controller and stationary shuttle at coordinate -12N. All other sites and channels are vacuum.

### Theorem 3: exact-pair equivalence

For every positive raw N0,

there exists t >= 0 with A^t(C(F:q0,N0)) = C(H,N0)

if and only if R started at (q0,N0) halts.

Equality here is equality of the entire finite configuration at absolute coordinates, including all three token types, both occupied sites, and vacuum elsewhere. It is stronger than observing the H controller somewhere.

Proof. On a source halt, Lemma 2 gives the terminal canonical section with raw N0. The right marker never moves, and the left pair is restored to -12N0. Thus the entire configuration equals the computable target C(H,N0). Before that section, every encoded macro uses the prescribed local rows and its stage-zero sections have precisely the source states in Lemma 2; no earlier section is H. Intermediate macro stages do not contain the clean stage-zero H pair. On a nonhalting source run, the prescribed simulation never reaches H. A stuck source triggers the prescribed leftward escape: its shuttle separates forever from both stationary markers and never creates a canonical H state. No arbitrary completion row is used before first acceptance or on those nonhalting/stuck continuations. This proves both directions and the first-hit claim.

The target depends on N0. The theorem does not give one fixed universal target configuration. Nor does it claim stationary halting, uniqueness of later occurrences, or anything about the orbit after the first target hit, when completion may take over.

### Corollary 4: fixed-rule r.e.-completeness and sharp mass three

Choose one fixed universal reversible separated two-counter source with a fresh initial state and terminal final state. The corresponding A is fixed. A computable input encoder sends a source instance to N0 and then to the pair (C(F:q0,N0), C(H,N0)). The halting set of a fixed universal source is r.e.-complete, and this gives a computable many-one reduction to the exact-pair reachability language. Conversely, finite configurations can be simulated forward effectively, and exact equality with a supplied finite target is decidable at each tick; enumerating ticks semidecides reachability. Thus exact finite-configuration reachability for A is r.e.-complete, even when restricted to this computably parametrized input-dependent family of mass-three pairs.

The classical dependency is Morita's reversible two-counter universality theorem, as stated in Morita–Imai (2001), Proposition 3.4, together with their Lemma 3.5, pp. 245–246. Lemma 3.5 explicitly supplies a simulating reversible two-counter machine whose initial state has no incoming instruction. Take the universal Turing machine first, then this fixed reversible fresh-start simulator. Their definitions use the separated instruction model. The wrapper's counts below are measured after that normalization; no bound on the freshening overhead is supplied here. Neither this proof nor the prototype instantiates an expanded universal transition table.

Primary source: [Morita–Imai 2001, Definitions 3.1–3.3, Proposition 3.4 and Lemma 3.5](https://www.numdam.org/item/ITA_2001__35_3_239_0.pdf).

The frozen report's mass-at-most-two theorem covers exact configuration pairs at absolute coordinates for every fixed deterministic conservative one-dimensional finite-radius CA with finite alphabet, unique vacuum and positive integer nonvacuum weights. It does not require reversibility. It describes near configurations and far two-particle affine motions, including first returns, eventual escape, and translated recurrent tails, and decides exact hits in all parts of this compressed orbit. Its polynomial bit-complexity assertion is for a fixed rule. Combining that lower result with this new upper result makes three the least conserved mass permitting fixed-rule undecidable exact-pair reachability in this weighted model.

## 3. Radius one, still with three mass units

Spatial blocking of four consecutive old sites is a global conjugacy onto the blocked full shift. It preserves mass and exact equality at every time. Because -12N0 is a multiple of four, both input and target left pairs lie at blocked coordinate -3N0 and offset zero; the right marker remains at zero. The blocked rule has radius one and exactly the same first-target time as A. It therefore inherits the exact-pair undecidability theorem and the sharp threshold three.

The alternative four-phase radius-one construction retains the native coordinates -12N0 and 0. The exact target uses phase-zero channels. From a synchronized phase-zero input, all tokens have phase t mod 4, so an off-section time cannot equal that target. At times 4t the encoded state is exactly the native state after t steps. The first exact-target time is therefore multiplied by four. No additional mass or background is introduced by either construction.

## 4. Source and local-rule size ledgers

Let q=|Q|, J be the original instruction count, m=J+1 the instruction-register modulus, d the number of INC/DEC instructions, and B the expanded branch count (each ZERO on the second counter contributes two branches). The cleaned source has exactly

q' = 2q+1,
J' = 2J+2,
m' = 2m+1,
d' = 2d,
B' = 2B+2.

All are unsimplified finite-program counts, not runtime quantities. The CA generator's verified formulas can be applied directly to q',m',d':

- Channel types: 96q'm' + 6q'd' + 2d' + 6q' + 2314
- Prescribed pair rows: 3528q'm' + 6q'd' + d' - 6m' + 1152
- Completed supported pair rows: 7008q'm' + 12q'd' + 2d' + 6q' - 6m' + 2304

The native alphabet is the power set of the channel set. Spatial and phase radius-one alternatives each use four times as many channel types. Spatial blocking's local permutation remains a composed block description; native pair-row counts are not flattened block-row counts.

## 5. Exact physical clock

Let Theta be the total native CA microtime for the original forward R trace, and Nh its final raw value. The native clock for an instruction N -> N' is

- INC: 108N + 96N' + 8
- DEC: 96N + 108N' + 8
- ZERO, POSITIVE, NOP: 192N + 8, with N'=N

Reversing INC exchanges it with DEC and swaps N,N', so these two expressions agree. Reverse tests and NOP have the same unchanged N and hence the same duration. The reverse half therefore takes exactly Theta. The bridges cost 192Nh+8 and 192N0+8, yielding the first exact-target time

T-clean = 2Theta + 192(Nh+N0) + 16.

Spatial blocking keeps T-clean. Four-phase dilation gives 4T-clean.

This is logical uncomputation carried out using forward CA ticks and different control types. It need not retrace the first half's microscopic positions or worldlines. Clock symmetry follows from the explicit formulas, not from global reversibility alone.

## 6. Compact horizon certificate: no duplicated reverse witness

Fix an external original-source horizon h and an input mode supported by the frozen exporter. Reuse its original forward polynomial P_h and its affine outputs N0, Nh and Theta. P_h has a natural zero exactly for first halt at h; the forward witness is unique in each fixed input fiber. A zero determines the full forward source trace and hence the full cleaned source trace from Lemma 2. The known local compiler then determines every microscopic configuration of the cleaned CA through its first exact target.

Thus the cleaned pair has first source-section hit at horizon 2h+2 exactly when P_h has a natural zero. The core ledger is unchanged:

- 2Bh natural witness variables
- 3h+1 affine-square slots
- Bh nonnegative affine-product slots
- Total degree at most two

No separately quantified reverse controls, raw values, branch selectors, divisibility witnesses, or microstep variables are needed. The reverse trace is decoded from the forward witness and the proved composition; this is not an arbitrary-trajectory verifier.

To impose an externally specified exact cleaned microtime T, add the single affine square

(2Theta + 192(Nh+N0) + 16 - T)^2,

or its fourfold-clock version for the phase model. This adds no variable for fixed T. To expose T as a free output, add one natural output variable and the same square. The target's raw value is N0 itself, so its exact restoration requires no new witness or output square.

The implementation preserves the original free-raw and bounded-counter-loader input modes. If r genuine input coordinates and k bounded-loader selectors are used, and ell is the loader square count (0 or 3), let s be 1 only for a free time output, and e be 1 when a time equality is included. The complete ledger is

- 2Bh+r+k+s natural variables
- 3h+1+ell+e affine squares
- Bh affine products

The h=0 core has the original single constant halt square and no core witness variables. Its cleaned time is 384N0+16. Optional loader and time coordinates are still paid normally.

This is a family indexed by externally fixed finite h. It is not one fixed-arity unbounded-time quadratic encoding. Natural-number exactness is essential: for a one-step DEC2 source with N0=3, the rational assignment e=1,u=1/2 satisfies the forward polynomial and represents N1=3/2, although the actual natural decrement is disabled. Thus nonnegative-rational zero exactness is not claimed. Computable input encoding N=2^a3^b is external unless the explicitly bounded loader is charged.

### Affine zero-fiber equivalence with the full cleaned certificate

There is a stronger, explicit relation to the uncompressed certificate obtained by applying the frozen exporter directly to R-clean at source horizon H=2h+2. Number original expanded branches 0,...,B-1. The full branch list has forward branches 0,...,B-1, inverse branches B,...,2B-1, and bridge branches 2B and 2B+1. The mirrored test branch retains its residue.

For every original step t and branch b, copy both e_(t,b) and u_(t,b) into full forward slot (t,b) and full inverse slot (2h-t,B+b). Give full bridge slot (h,2B) selector 1 and base Nh-1. Give slot (2h+1,2B+1) selector 1 and base N0-1. Set every other full slot to zero. Preserve loader selectors and genuine input/output coordinates, allowing harmless alpha-renaming of an interface coordinate if its name conflicts with a new full-certificate e/u slot.

Every formula in this lift is affine in the compact variables. In particular, reversing an INC branch whose old/new forms are e+u and p(e+u) gives a DEC branch with these forms interchanged, using exactly the same base u. The same observation applies to DEC; tests and NOP keep their base. Positive N0 and Nh guarantee that the two bridge bases are natural on the compact zero fiber.

Consequently each compact natural zero lifts to a full cleaned-source natural zero, including the same optional time endpoint. Conversely, a full cleaned-source zero at H=2h+2 must arise from an original first halt at h by Lemma 2; restriction to the original forward slots and interface/loader coordinates gives the compact zero. Uniqueness of the full cleaned-source witness then makes these operations mutually inverse on each fixed input fiber. This is an affine zero-fiber bijection, not merely an abstract computable trace decoder.

The affine formulas are not claimed to send every off-zero natural assignment to a natural assignment: Nh-1 or N0-1 can be negative away from the constrained zero fiber. No equality of the two polynomial values off their zero sets is asserted. Materializing the full certificate still incurs its full 2B'H core-variable cost; the compact presentation does not allocate these derived variables.

## 7. Executable evidence

The files in this directory implement the source transform, compact certificate exporter, a separately coded wrapper checker, and actual lattice tests. The checker imports only the frozen independent forward checker, not the new exporter. It reconstructs the wrapped program and both halves of the source trace, validates all forms and ledgers, checks the natural zero, and verifies optional literal polynomial expansion.

The lattice harness simulates every native tick through first exact target and checks every clean section against the decoded trace. Selected runs also simulate every spatial tick and every phase tick, checking exact conjugacy, inverse steps, total mass, first target equality and phase exclusions. All native encoded runs require prescribed pair rows, ruling out reliance on arbitrary completion. Tests cover all nine operation/counter variants, both ZERO3 residues, branch/merge syntax, a mixed arithmetic chain with Nh != N0, h=0, initial and delayed stalls, a growing nonhalting prefix, the returning-initial-state counterexample, input loaders, finite natural witness enumeration, mutations, source/local-rule ledgers, and clock symmetry.

Finite tests verify implementation instances and do not establish unbounded nonhalting by themselves. The all-input and all-source conclusions follow from the proofs above and the frozen compiler/lower-bound theorems. See receipts/test_clean_targets.json for exact counts and hashes. The affine lift is also checked against freshly constructed full cleaned-source witnesses and the frozen independent full checker; receipts/affine_lift.json records 77 cases, including adversarial interface names requiring alpha-renaming.
