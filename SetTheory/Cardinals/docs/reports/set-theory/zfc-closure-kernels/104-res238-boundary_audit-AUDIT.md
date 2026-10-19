# Independent audit of the boundary/source-rotation reduction

## Result and scope

The boundary 239 source, six-case context fold, and blank initialization pass independent verification. I found no gap in the ordinary universal runtime proof rules. The delayed-erasure local reduction is structurally compatible with this construction. The combined 238-state table has now passed the complete universal runtime proof; that direct route does not need the representation-dependent selector guard as a premise. The requested ordinary mathematical ZFC endpoint is ACCEPTED.

This is an ordinary mathematical audit and finite executable certificate. It is not a new Lean/Rocq kernel endpoint or a serialized derivation in ZFC. It asserts neither ZFC consistency nor unconditional machine nonhalting.

The input boundary table is `candidate239/zfc_boundary239.tm`, SHA256 `666f5bf1370b6b44ff4e614e4b194bc5be6b4c621914842ad7e344d6570a544e`. The inherited-label equivalent has SHA256 `d061770f487937f9da652919c9bc9bb79bc9bf137ca41dd7a08eb5ecda8e7719`, start 95, dispatcher 96, halt 254.

## Exact source equivalence

The independent checker `audit_boundary.py` does not import the archive's source-certificate implementation. It replays rotations by substitution on complete leaf paths, independently calculates successor paths using fixed-width integer increment and suffix-position deletion, and locates successors via disjoint binary intervals. It checks complete/prefix-free source structure, every ordered instruction and operand, both outcomes of every decrement, and the unique literal halt.

All 13 stages, comprising 25 rotations, pass. Every stage preserves 8,385 nonhalting successor/guard edges and the halt descriptor across 6,455 leaf occurrences. Final source counts are 1,931 decrements,2,596 increments,128 breaks,1,799 continues,1 halt; these generate 8,386 guarded runtime obligations. The final hash-consed DAG has 224 nodes and maximum path length 48.

The source proof is a strong bisimulation: relate configurations with equal register vectors and the same located leaf-occurrence index. The instruction and affected register agree; the decrement guard therefore agrees; the successor indices agree. Thus each step preserves the relation or both sources reach the literal halt. This holds for every natural register vector, without bounded numerical tests or reachability restrictions.

For every successor, the independent checker verifies equality of the finite words after dropping trailing zeroes. This is precisely equality after infinite zero extension. It covers residual paths shorter than the located leaf, surplus zero tails, root rollover and empty paths. Consequently the tape interface can replace each residual with the next full leaf path without discarding a 1 or changing any tape cell.

The archive's static Lean-source interface checker was separately replayed into `source_interface_replay.json`. It extracts all 6,455 baseline triples from the actual literal lookup definitions and overrides, along with seed(3,0,0,0,3,0,0,0,0), and matches them exactly. RegisterPath.lean's zero-extended walk, consume-to-leaf-depth, increment, break, continue and literal-halting definitions agree with the checked graph semantics. Declining DAG indices and depth 51 below fuel 204 rule out decoder exhaustion. This replay is a data-extraction check, not Lean elaboration or a new remote-byte provenance check.

## Boundary six-case context fold

The independent checker confirms that the repaired 240 table changes exactly six rows and deletes only old state 218. It enumerates every transition in the whole old table to establish:

- 179 has only incoming 161/0,236/0,239/0, all writing 0 and moving right;
- 218 has only incoming 187/1,220/1,237/0, with respective left tags 1,1,0;
- 223 has only incoming 218/0 and is internal to the three-step old block.

There is no hidden decoder entry into the internal helper. Start 95 is outside these states. At checkpoints the tape and head agree, while old 179/tag 0 maps to 179, old 218/tag 0 maps to 223, old 218/tag 1 maps to 179, and other controls are unchanged. Old 223 is never a checkpoint.

The independently executed six local cases use only the two specified cells at positions−1 and 0, reject any exterior read, preserve both cells exactly, finish at head+1 and reach the same ordinary endpoint. Their old/new lengths are 1/1,1/5,3/1,1/1,3/1,1/3. All exterior tape is arbitrary. Ordinary rows preserve the checkpoint relation, and all special blocks have strictly positive finite length. Therefore the repaired 240 and boundary 239 machines halt together on every initial binary tape from state 95. This theorem is stronger than blank-start equivalence and is formalizable by elementary finite-computation induction.

## Blank initialization

An independent sparse interpreter executes 409,691 steps of the boundary 239 table from state 95/head 0/blank. It reaches state 96/head−5 with exactly 351 one-cells. The complete support equals the published position list and also equals an independent reconstruction with marker−6, header 176, physical values[0,0,0,3,0,0,3,0,0], and 167 spare values all 1. Header distance 181 gives extra gap 117 for the runtime invariant. The comparison includes all cells, with both infinite exteriors blank.

This is an exact finite computation. It does not establish unbounded runtime correctness by itself.

## Universal runtime rule audit

I read the whole `validation/symbolic_runtime.py` proof engine and its imported table/path helpers. Its mathematical rules are sound for the claimed complete frame invariant:

1. A literal transition uses the supplied actual table and changes exactly one cell, head and control.
2. A self-loop in the scan direction crosses an arbitrary finite unary run by induction on its nonnegative length. A non-self-loop consumes one cell only when the affine length has constant term at least 1 and all coefficients nonnegative.
3. Four one-block schemas are freshly derived from the actual table with arbitrary natural block value and opaque left/right contexts. Each returns to the same control/orientation and preserves the contexts. Structural induction therefore licenses an arbitrary finite list of such blocks, with duration and displacement equal to its actual finite width.
4. The rewrite C(A)1=1B(A), and its reversal, is a finite-word identity, proved by empty-list and cons induction using B(v)=01^(v+1), C(v)=101^v.

No guessed zero/positive branch, unresolved opaque context or failed proof search is accepted. The 4000-iteration limit bounds construction of a proof, not register values or actual tape runtime.

Every primary register is an independent natural variable. A selected positive decrement is 1+x; zero decrement is exactly 0. The gap is an independent natural, as is the first spare value; the spare tail is an arbitrary finite list, including empty. Thus the full spare suffix is nonempty. All returns compare the entire tape and control/orientation, and also check actual head displacement. A source halt must reach the literal halt control; a premature halt in a nonhalting case fails.

If o is overflow and delta is 1 for positive decrement, the new head is old head−o and new distance is D+delta+o. Hence the next extra gap is n+delta+o≥0. Existing spares persist and increment appends a value 1 spare. The independent canonical-source normalization closes the invariant after each instruction. Accepted symbolic durations have positive constant term, ruling out infinite zero-time stuttering. Determinism and induction on a finite halting time establish both directions of halting equivalence.

The full combined-table replay was performed by the separate construction lane and passed all 8,386 cases using 2,255,513 symbolic rules, with minimum constant duration 13 and all 476 rows covered. I independently checked every guard is present exactly once, all reported affine-duration coefficients are nonnegative, all hashes match the exact table/source/engine, and the copied engine is byte-identical to the one reviewed. I also independently executed the 409,835-step combined startup, reconstructed its full frame, and checked the canonical action isomorphism. This is not described as a second independent-engine replay.

## Compatibility with delayed erasure

Every row of all 23 states on the delayed-erasure six-case local paths is byte-for-byte action-identical between rotation 240 and boundary 239:46 rows in total. The exact complete incoming sets of 67,80,91,169 are likewise unchanged. The boundary fold's entire local support is disjoint from the delayed patch rows 147/0,80/0,91/1 and deleted 169 rows.

Thus no hidden external entry, changed helper row or overlap invalidates the delayed-erasure structural proof. Source paths have changed, so the representation-dependent implication “old 169 scanning 1 implies right neighbor 1” must not be inherited merely from the old source. The separate delayed-erasure auditor has now freshly checked the guard on all 8,386 boundary cases: 96 state169 visits, of which 32 read1, all at increment4; their rightward one-runs have lengths G+K with 23≤K≤59. Startup has 18 visits, including 6 reading1, all satisfying the guard. Thus both the local-transfer route and the direct complete-runtime route are established. The direct runtime proof remains sufficient without the guard as a premise.

## ZFC composition

The inherited exact source calibration is `CalibratedRotation240.halts_iff_zfc_refutation` at logical seed(3,0,0,0,3,0,0,0,0). The archive includes its source, which composes complete source equivalence with the established original-program calibration and LogicalSeed246. The prior audited calibration supplies the conventional finite-ZFC-refutation endpoint. The new source, finite table, startup and word/list arguments use only natural-number induction, finite syntax and finite sequences, and are formalizable in ZFC.

The combined table's direct runtime and exact startup certificates have passed and are bound to the audited exact source and proof engine. Accordingly, composition gives ZFC ⊢ Halt(M238,blank) ↔ ∃p Proof_ZFC(p,⊥), and classical negation gives ZFC ⊢ Nonhalt(M238,blank) ↔ Con(ZFC). A ZFC consistency assumption is not needed to prove this biconditional. No minimum-state or newly mechanized kernel theorem is claimed.

## Evidence

- `audit_boundary.py`: independent source/fold/startup/support checker
- `independent_boundary_audit.json`: complete results and all six local traces
- `source_interface_replay.json`: fresh static Lean source/seed interface replay

- `audit_combined_endpoint.py`: independent final startup, canonical table and full certificate-binding check
- `combined_endpoint_acceptance.json`: accepted exact 238-state endpoint and verification counts
