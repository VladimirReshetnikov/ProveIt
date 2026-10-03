# Independent implementation and theorem audit

Date: 2026-10-03 UTC

Verdict: PASS, under the stated fresh-entry, separated deterministic reversible source hypotheses. No correction to the transformation, exact-target theorem, native clock, transformed counts, or compact certificate was needed. A variable-name collision in the subsequently added full-witness-lift helper was found, repaired, and independently regression-tested; no correctness issue remains in the audited snapshot. The fixed CA is recompiled for the cleaned source; the result concerns a computable input-dependent exact target, not one universal target independent of the input.

## Audited claim

Let R have finite state set Q, designated initial q0 with no incoming instruction, and halt qh with no outgoing instruction. Make disjoint state copies F:q and B:q and a fresh state H. Copy each instruction into F, copy its relational inverse into B with swapped endpoints (INC/DEC interchanged, tests and NOP retained), and add F:qh NOP B:qh and B:q0 NOP H. Compile with H as the sole final state.

The new source is separated deterministic and reversible. In the F copy the source syntax is unchanged; in B the old incoming and outgoing separated conditions exchange roles. The first bridge uses the empty outgoing side at F:qh and empty incoming side at B:qh. The second uses the empty outgoing side at B:q0 and the fresh incoming side at H. H has no outgoing instruction. Prefix-based names are injective and mutually disjoint even if original names contain `F:`, `B:`, or `H`.

If the original first-halt trace is (q0,N0),...,(qh,Nh) of length h, the only cleaned trace is its F copy, its B copy in reverse order, then (H,N0). Its length is exactly 2h+2. Every reverse decrement is enabled because its original increment produced the requisite divisible value; reverse increments are always enabled; tests see their unchanged counter values. The h=0 case is valid when q0=qh and still uses both bridges. The raw coprime-to-six cofactor is invariant, so restoration holds for every positive raw N, not only pure powers of two and three.

An infinite source run stays in F forever. A stuck source run also never reaches either bridge and the compiled CA enters the specified escape route. Its trap and right marker remain stationary while the escape moves farther left; no completion row is ever required afterward. These facts exclude later false exact targets on nonhalting inputs, rather than merely checking a finite prefix.

## Exact configurations and time

For the cleaned fixed rule A, define x_N as its canonical configuration with R at coordinate zero and the clean stage-zero pair L(F:q0,0,0), S0 at -12N; define y_N identically except for L(H,0,0). All other sites and channels are vacuum. Then A^t(x_N)=y_N for some t>=0 if and only if R halts from (q0,N). Finite scratch and instruction registers are exactly zero at the final section. R has never moved, and the arithmetic inverse trace restores the original gap, yielding equality of the full anchored configuration. The input encoder computes y_N from N without h or Nh.

No target configuration can be reached earlier at a different internal stage: its exact channel types require stage zero, state H, and clean registers. The post-halt orbit is intentionally unspecified by the simulation. It may leave and later revisit the target. No stationary stop or unique occurrence is asserted. Independent tests explicitly verify departure on the next completed CA tick.

For a forward arithmetic step N to N', native INC time is 108N+96N'+8 and its reverse DEC time is 96N'+108N+8. The DEC/INC case is the same equality with endpoints exchanged. Tests and NOPs take 192N+8 in either direction. Thus the reverse simulation has the same total native duration Θ as the original forward simulation, although it is a new forward-time CA execution rather than the literal inverse CA microtrajectory. The two bridges cost 192Nh+8 and 192N0+8, so the first exact target is at

T = 2Θ + 192(Nh+N0) + 16.

Full four-site spatial blocking is a conjugacy and gives exactly the same T, with clean pair at -3N0 and offset zero. Four-phase internal dilation gives exactly 4T; before a multiple of four the nonempty synchronized configuration has a nonzero phase and cannot equal the phase-zero exact target.

## Counts and compact certificate

For q states, J instructions, m=J+1, d arithmetic instructions, and B residue-expanded branches, the unpruned cleanup has

q'=2q+1, J'=2J+2, m'=2m+1, d'=2d, B'=2B+2.

Prime-three ZERO has two branches before and after reversal. These exact counts start after any preliminary fresh-entry normalization and do not bound that normalization's overhead. Substitution in the frozen compiler's type and pair-row formulas matched all independent actual compilations.

The compact certificate legitimately uses the existing original h-step forward certificate. A zero of that nonnegative natural-number polynomial proves the first forward halt. The cleanup theorem then uniquely determines the entire reverse half, both bridges, and exact target. Hence the core resource ledger remains 2Bh natural witness variables, 3h+1 affine-square slots, and Bh product slots, including h=0. Original input loader costs remain separately charged. The affine cleaned-time expression is 2Θ+192(final_N+initial_N)+16, multiplied by four only for internal-phase encoding. An optional fixed time adds one affine square; a free time also adds one output variable. No additional independently guessed reverse witnesses are necessary.

The separate checker reconstructs the transformed machine, rechecks freshness, derives the raw-target identity and cleaned-time affine form, validates its full polynomial presentation and ledger, and delegates the untouched forward certificate to the frozen independent checker. Its reconstructed reverse trace agrees with an independent source interpreter, including h=0 and name-prefix edge cases.

## Full-witness affine lift and repaired name hygiene

The optional full-witness helper realizes the compact zero-fiber equivalence explicitly. With zero-based branch indices, original step t and branch j are copied into full slots (t,j) and (2h-t,B+j), for both e and u. The first bridge occupies (h,2B), with e=1 and u=Nh-1; the second occupies (2h+1,2B+1), with e=1 and u=N0-1. Every other full-core coordinate is zero. Original input coordinates, bounded loader selectors, and any free time output are retained up to explicit alpha-renaming. Projection onto the forward slots recovers the original core zero witness. Thus this is a bijection on natural zero fibers, not a claimed off-zero polynomial identity or a map of the entire natural orthant into itself.

An independent implementation of this formula passed 24 cases against both the frozen full cleaned-source checker and its unique witness generator: h=0, INC3, ZERO3, two-step arithmetic, all original input modes, and both native and phase clocks. The original forward variables and reverse variables share the same quotient offsets because INC/DEC swap their old/new affine forms, while test residues are unchanged.

The first new helper implementation could reject a valid compact zero if its public input or output was named like a newly introduced full-core coordinate, for example e_0_1 in a one-step one-branch compact certificate. This was reproduced for free-raw, bounded-counter, and free-time coordinates. The repaired helper computes the complete full-core namespace, alpha-renames only colliding public coordinates, and records their affine aliases back to the compact names. Loader selector names remain intact. Independent regression now passes 96 combinations of h=0/1, colliding input/time/bounded/mixed coordinates, and all three physical models. Both the full independent checker and full witness generator confirm the lifted zeros.

The final audited implementation hashes are:

- clean_targets.py: a79405023df5a1038a69bc947314979093df39be8da7abcdf5588f77da848315
- check_clean_targets.py: 51ce0665dcc74bc3cf2461a25344a8688b23258b9281205c68fabb0526881d72

## Freshness is necessary

The separated reversible source

q0 ZERO_a -> q1; q1 INC_a -> q0; q0 POSITIVE_a -> qh

has raw trace (q0,1),(q1,1),(q0,2),(qh,2). Its naively reversed trace first reaches B:q0 at N=2. An unconditional exit there would restore the wrong raw input. Moreover B:q0 already has the inverse DEC instruction, so adding NOP is an outgoing motion conflict. The transformer and checker independently reject this source structurally. They also reject an incoming guard disabled on the current input; freshness is not an input-specific shortcut.

The universality corollary must use a genuine fresh-entry normalization. The locally available primary-source text for Morita–Imai (2001), Lemma 3.5, explicitly provides an initial state with no incoming instruction while preserving reversibility. Proposition 3.4 supplies universal reversible two-counter simulation. Combining those statements with the compiler establishes r.e.-hardness for one fixed cleaned rule and its computable family (x_N,y_N); simulation semidecides exact equality, giving r.e.-completeness. No expanded universal transition table is supplied by this addendum. A naive new NOP into an arbitrary old initial state is not justified.

## Lower-bound scope

The companion low-mass proof explicitly handles exact anchored finite configurations, not merely patterns. For mass at most two, finitely many near shapes are connected by computably accelerated independent-walker excursions. Exact target tests cover intermediate excursion phases and all subsequent translates after a normalized repeat. Thus the lower bound matches the new upper bound: three is the sharp weighted mass threshold for fixed-rule exact configuration-pair reachability undecidability.

This conclusion assumes a fixed finite-alphabet, finite-radius, translation-invariant one-dimensional conservative CA with positive integer weights on nonvacuum states and a unique zero-weight vacuum, acting on the infinite line. Reversibility is not needed for the mass-at-most-two decision procedure. This does not transfer by relabeling to ordinary integer-state NCCA, active zero-mass backgrounds, or prescribed finite rings.

## Independent tests

The actual-CA harness does not import the cleanup implementation. It separately constructs the cleaned source, executes source instructions, updates the generated collision/stream maps, and recognizes exact whole configurations without calling the compiler's `step` or `ready` helpers.

- 14 small compiled source programs and 35 runs: 26 successful cleanups and nine stuck inputs
- All INC/DEC/ZERO/POSITIVE/NOP primitives on both counters, h=0, a two-step arithmetic chain, and an incoming prime-three test merge
- Raw cofactor-five cases, delayed inverse control changes, exact endpoint channels and coordinates, no early exact target, no unexpected triple collision, and only specified pairs through the intended execution
- 111,712 native ticks, 9,456 packed ticks, and 37,824 phase ticks checked
- Largest compiled example: 7,236 types and 346,040 completed pair-support rows
- Global inverse checked at every canonical boundary and immediately after target departure
- Source/count/certificate checker audit: 61 successful model/interface cases, 174 deliberate mutations rejected, 19 invalid syntax/API/freshness cases rejected
- 1,536 exhaustive natural assignments for the two residue branches of a prime-three zero test, including disabled raw multiples of three

Scripts are in audit/ and complete original audit receipts are in receipts/:

- audit_actual_ca.py / actual-ca-receipt.json
- audit_certificates.py / certificate-receipt.json
- audit_witness_lift.py / witness-lift-receipt.json
- audit_lift_name_collisions.py / lift-name-collision-receipt.json

The original harnesses were independently run against the sealed source. In this portable package, dependency locations and receipt labels are adjusted to relative paths, with all changes documented by hashes in SOURCE_PROVENANCE.md. Run replay.py to execute them in an isolated temporary copy; subject hashes are recorded in the receipts. The frozen release's 65-file SHA256SUMS manifest passed after these checks. No frozen report or release file was changed.

## Limits of this audit

Finite tests reinforce the proof and implementation review; they do not prove universality or validate an expanded universal source table. The actual CA harness checks the new wrapper against the already proved frozen generator. The certificate checker remains source-horizon-specific and is not an arbitrary three-mass CA trajectory certificate. Exact target dependence on N is essential to the stated construction.
