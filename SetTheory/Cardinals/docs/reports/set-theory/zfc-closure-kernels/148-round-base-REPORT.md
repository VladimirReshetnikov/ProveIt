# Independent current219 baseline audit

This audit is foundational evidence for the requested <=218 research. It does not produce a <=218 machine or assert minimality. Received artifacts were used only as JSON/text data; no received Python module, installer, or wrapper was imported or executed.

## Results and precise status

Independently checked here:

- Exact canonical hash `02079501e6255951cbc1c31d2c3cab076574d3d61c892f0e5a541cd1789442ec`, native hash `b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26`, and source hash `0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789`.
- A complete, collision-free native/canonical transition correspondence; 219 working states and 438 rows.
- Four exact source replacements from the pinned220 source. Distinct subtrees change208 to206; primitive occurrences remain4744.
- Exactly eight retained-row changes, removal of102/120/121, and addition of301/302.
- All86 break and8 continue roles assigned to108 match the literal source and correct suffixes.
- Literal whole-exterior local proofs of the198 increment bypass and108 suffix rewrite. A negative control shows that weakening198's010 premise is invalid.
- An independent postfixed-point check of the source worker's ten-atom invariant, using structurally derived ancestor-edge control flow rather than its binary address arithmetic. All6161 enabled nonhalting edges preserve the invariant. Five edges are infeasible. NIP entry4598 has R6 exactly0. The halt entry remains nonbottom.
- Exact221->220 primitive-word and complete guarded-CFG identity, plus the local171/202 fold blocks with their decoder tag premises.

Mathematically reviewed here, not proof-assistant formalized: the all-natural old/new equality contract, the stronger cleanup domain, contextual substitution,302's unary/carry transformation, and the boundary of the inherited calibration argument.

Finite diagnostics:4225 counter pairs through64, five larger pairs up to100000 with other registers nonzero, and640 numerical302 examples. These are debugging support, not the universal equality or302 proofs.

A newly authored independent symbolic checker successfully checked the first50 primitive cases with arbitrary natural data and complete-frame postconditions. The full6167-case replay was deliberately not duplicated because another worker owns that run. Those50 checks are partial coverage, not a complete219 runtime proof.

Reported by the pinned intake, not rerun by this audit: the complete6167-case symbolic runtime,1515040 symbolic rules, all438 rows, minimum duration13;312617-step sparse/dense startup; and the ordinary finite-refutation consistency calibration. Exact219 Lean and internalPA endpoints are absent.

## Source semantics and all-natural proof

Let `N` denote normal completion, `B(k)` a k-level break, and `C(k)` a k-level continue. At a pair `(X,Y)`, a left-childB(1) is consumed and skipsY; a larger left break decrements its level. Left continues propagate. A right-childC(1) restarts the pair; a larger right continue decrements its level. Right breaks propagate. Decrement on zero emitsB(1); positive decrement reduces its register and returnsN.

Write D5=CD5, D6=CD6, C1=CC1, C2=CC2, B=CB1. The literal new macro is:

P=(D6,C2), U=(P,B), A=(D5,U), L=(A,D6), Z=(D5,C1), R=(Z,U), E=(L,R).

The following equations are complete contracts, including register effects and control exits:

1. P on b=0 returnsN without change. On b>0 it decrements b and returnsC(1).
2. U on b=0 returnsB(1). On b>0 it decrements b and returnsC(1). Thus U is genuinely open.
3. A on(a,b) returnsN at(0,b-a) if a<=b; if a>b it returnsB(1) at(a-b-1,0). While both counters are positive each repetition decreases both; zero causes a finite exit.
4. L returnsB(1) at(0,0) exactly when a=b. Otherwise it returnsN at `(max(a-b-1,0),max(b-a-1,0))`.
5. Z clears a and returnsN. R first clears a viaZ, then usesU to reduce b. A positive b repeatsR; zero b returnsB(1). Therefore R always clears both counters and returnsB(1).
6. E consumes L's break on equality and skipsR; on inequality it executesR and propagates its break.

Only registers5 and6 occur. Hence E terminates on all natural inputs, clears both, preserves every other register, returnsN iff equal and otherwiseB(1), and emits no escaping continue or halt.

For the old literal macro, set V=(D5,C2), X=(D6,C2), Y=(CI5,X), W=(V,Y), T=(D6,W), J=(Z,B), F=(D5,J). The old macro is(T,F). Y transfers b to a and then adds one, yielding(a+b+1,0), with normal exit. T cancels both counters until one is zero; if b remains it usesY after one decrement to transfer that residual exactly. Thus T returnsN at(|a-b|,0). F tests that difference: zero returnsN; positive difference is decremented, cleared byZ, and returnsB(1). This proves exactly the same full contract without scratch-zero or reachability hypotheses.

Since both routines terminate internally, contain no halt, preserve the same complete logical register state, and have identical possible exits, replacing any occurrence preserves finite halting and divergence in either direction. This is a contextual source theorem, not merely a finite test or an unchanged leaf-word claim.

### Exact open-versus-closed boundary

U'sC(1) binds toA during cancellation and toR during cleanup. The same syntax is shared under two different surrounding continuations. Treating U as a standalone normal-return routine is unsound. P is also open, with possibleC(1). The complete equality routine hasN/B(1) exits, so it too is not a normal-only closed block; it is safely substitutable because the old and new exit contracts match.

The predecessor's “closed rotation factors” mean no escaping control signal/halt according to the boundary analysis. That syntactic notion does not by itself assert termination. It must not be conflated with the all-natural terminating equality theorem.

## Stronger invariant useful for reduction

R is only called when the original a!=b, and then:

R5=max(a-b-1,0), R6=max(b-a-1,0), hence R5*R6=0.

Conversely every nonnegative orthogonal pair is realizable on an unequal input, including(0,0) when|a-b|=1. Therefore an alternative cleanup only needs to clear the union of the two coordinate axes, but it must returnB(1) even at(0,0). A normal return at zero would incorrectly turn adjacent unequal inputs into equality. The current R proves the stronger arbitrary-pair contract; a smaller source or compiled cleanup could exploit this excess strength.

Separately, the independently validated source certificate proves R6=0 at NIP entry4598 from initial seed(3,0,0,0,3,0,0,0,0). This is a genuine source-reachable invariant, not a claim from arbitrary register configurations or an arbitrary tape.

## Compiler repair contracts

### State108

At a read-one leaf with suffix001 or101, the three literal transitions108/1,10/0,16/(0 or1) clear the terminal1, leave the intervening0, and toggle the earlier bit. Thus001 becomes100 and101 becomes000, reaching state1 three cells left of the original head. Only these three cells are touched. The literal decoder allocation has exactly86 CB1 sites with001 and8 CC2 sites with101. These are contextual decoder facts; arithmetic reuse needs the separate whole-frame runtime proof.

### State302

Its rows are302/1=(0,L,302) and302/0=(0,L,4). State4 clears a leftward run of1s and writes1 on its first0, exiting right into6. For a finite prefix p and k>=0, entering302 at the rightmost end of `p 0 1^k` transforms that word to `(p+1) 0 0^k`, with the standard carry position determining the exact head endpoint. Unary induction handles k and carry induction handles the trailing ones of p. No unrepresented cell is touched except the first carry-zero, which the complete frame must supply. This local lemma alone does not characterize every302 entry.

The only external incoming rows are103/1 and113/0. Importantly103 also has arithmetic incoming119/1 in addition to decoder88/1 and301/1. The eight decoder CB1 contexts have terminal runs11 or111, but these do not establish a universal bound for arithmetic entries. A proposed302 deletion must cover both entry families and all complete-frame uses.

### State198 spare-one bypass

On cells(h-2,h-1,h)=010, the old three-step path is198/0,198/1,113/0 and the new path is198/0,40/1,54/0. Both reach state40 at h-3 and change only cellh from0 to1. Every exterior cell is identical. This is an exact3-to3 local identity, not a timing approximation. If h-2=1 the identity fails; that is the tested negative control.

The normalized frame uses native dispatcher84, sentinel1 one cell left of the head, the source address, a zero gap to header1 at64+g, nine physical register blocks, and a nonempty finite spare list. BlockB(v)=0 1^(v+1); logical-to-physical permutation is(6,2,0,4,3,7,8,5,1). CI increments its register and appends a spare of value1. PositiveCD decrements its register and increases the gap by1. These spare/frame conventions matter: merely making an alternate return pass a generalized spare-zero interface would not prove compatibility with blank initialization.

The first50 independently symbolic-checked cases show198's CI use has left suffix01 and an infinite blank right tail; CD use has current1+v. This partial observation is not promoted to a complete all-site invariant. The full collector owned by the encoding worker is the appropriate place to establish that scope.

## Calibration pedigree and limits

The exact221->220 source has unchanged primitive word and all6167 guarded successors. The220 state fold is valid at source-decoder entries with predecessor tags0 or1, but not claimed for arbitrary171 entries; its complete final runtime is an additional obligation. The219 change instead replaces a source macro with the all-natural contextual theorem above and repairs affected machine returns. The underlying logical calculus and proof enumerator are unchanged.

Thus the ordinary219 calibration has the following dependencies: inherited pinned221 finite-refutation/ZFC-consistency calibration; exact221->220 source/CFG transport; old/new equality contextual equivalence; complete final219 primitive simulation with positive finite durations; and exact blank startup to the source seed. This audit independently checks the middle source and literal-local links, not the entire ancestor theory proof. The reported final runtime and startup are being separately reviewed/replayed, not silently inferred from a source-DAG count.

No unconditional nonhalting, global optimality, exact219 Lean theorem, or PA-internal equivalence follows from the checks here.

## Reproduction

The three completed owned checkers are audit.py, check_source_certificate.py, and check_pedigree.py. Their machine-readable receipts are RESULT.json, INVARIANT_AUDIT.json, and PEDIGREE_AUDIT.json. symbolic_contexts.py is the newly authored independent partial symbolic checker; SYMBOLIC_CONTEXT_AUDIT.json states its coverage explicitly. Re-running with no limit requests all6167 cases; it was intentionally not done in this audit to avoid duplicate work.

## Subsequent focused return audit

The encoding worker's complete owned baseline replay reports6167 cases,1515040 rules, all438 rows and minimum duration13. I separately parsed its1432 full symbolic incoming-return frames and independently executed the incoming native row to derive302's entry word. All left halves are fixed finite bitstrings followed by blank exterior; only the untouched right halves contain arbitrary register/gap/spare parameters.

The exact reduced contract, in nearest-first leftward notation `1^a 0 1^b 0 ...`, is:

- Incoming113/0:1419 frames have a=0, with b from0 through9. Four frames have a=1,b=0, precisely the right-childCD6 zero cases at source indices4571,4589,4603,4712.
- Incoming103/1: four frames have(a,b)=(1,0), three have(2,0), one has(2,5), and one has(2,6). The arithmetic119/1 entry corresponds to source4597 and(2,0).

For a=0, replacing entry302 by40 gives literally the same first row0L4. The13 nonzero-erase frames are therefore the exceptional obligations, not all1432 cases. I independently regenerated all13 exceptional cases from the dispatcher using a newly authored native-label symbolic engine, with arbitrary natural values, arbitrary gap and finite spare tail. All full frame endpoints passed, and every full captured word exactly matched the other worker's record. These are1420 symbolic rules, not finite-value tests. See RETURN_WORD_AUDIT.json and SELECTED_RETURN_AUDIT.json. The other1419 entry premises were read and reduced, not independently regenerated in this focused pass.

## Independently reviewed alternative equality candidates

Two source-worker candidates E11 and E2 have the same full all-natural equality contract:

- E11 retains L and uses cleanup `((D5,CI6),U)`. If a>0, a whole cleanup iteration sends(a,b) to(a-1,b): the temporary increment of b is immediately canceled by U. Once a=0 it drains b. Lexicographic(a,b) decreases on every continue.
- Let A2=(D5,((D6,C2),CI6)). A2 always returnsN, at(0,b-a) if a<=b and at(a-b-1,1) if a>b. Then E2=(A2,(D6,R)) has the same equality test and clean exit contract.

A further promising source-worker hit is

A=A2, U=((D6,C2),B1), E*=(A,(D6,(A,U))).

CleanupR*=(A,U) returnsB1 immediately at(0,0) on equal cleanup inputs. If b>a, one continuing iteration yields(0,b-a-1); if a>b it yields(a-b-1,0). Every continuing iteration strictly decreases a+b. Thus R* always clears both registers and returnsB1. The outerA always returnsN; its second output is0 iff the original inputs were equal. Consequently the following left-childD6 consumes its zero-break exactly on equality; otherwise it decrements and executesR*. This proves E*'s total, cleanN/B1 contract for all natural inputs, with all other registers unchanged and no escaping continue.

The source worker reports206 distinct whole-source nodes and no right-childCD for E*. These source metrics and machine compilability are its separate obligations. No <=218 state result follows from the source proof alone.

## Public221 formal pedigree clarification

The current pinned public candidate-k221 README and k225-formal README, read after the initial pedigree check, report two closed endpoints for the exact221 table:

- Rocq `K221F.CorrectDense221.tm221_halts_iff_ZFC_inconsistent`, independently rechecked with coqchk and recorded as PASS_CLOSED_KERNEL on2026-10-20.
- Lean `KLower221.blank_halts_iff_zfc_refutation : BlankHalts machine221 <-> BProv ZFCax_s [] Form.fBot`, with only propext,Classical.choice,Quot.sound.

The published source layer relates221's boot source to dag222 and C222F. Its upper/lower calibration establishes C222F iff ZF-refutation, followed by ZF/ZFC refutation equivalence. The published221 source hash691684ec948c972bf67727d6d4cd1181a90a9203644ee3db3eae363280e3fac9 matches the input independently checked here. The221 public canonical table hash is6457dce8c91c5975fb405607567158ca92ad97331f2724503edc0d4ff74cab3c.

These are explicit existing exact-table formal endpoints, not merely an uncalibrated seed-K conjecture. This audit read their documented statements and scope; it did not rerun Lean,Rocq or coqchk. Their existence supplies the inherited ordinary calibration premise. The new219 transport still needs its own source replacement, runtime and startup links and does not inherit an exact219 kernel theorem merely by prose composition. The current public formal README explicitly says219's exact-table Rocq,Lean and PA-internal endpoints remain open.

## Completion of the focused source and cooperative-return audit

DIRECT_CONTRACT_PROOFS.md proves direct09 and direct13 equivalent to the baseline equality macro on all natural register pairs, including total cleanup and precise normal-versus-break exits. DIRECT_CANDIDATE_AUDIT.json independently checks their four source substitutions and literal structural metrics. Selected whole-frame symbolic pilots pass115 cases for direct09 and131 for direct13, including changed macro sites and operation/operand coverage. The receipts are DIRECT09_RUNTIME_PILOT.json and DIRECT13_RUNTIME_PILOT.json. These are scoped pilots, not complete runtime, blank-startup, or smaller-table certifications; both raw compilations still have220 states.

The final state27 investigation is documented in STATE27_ANALYSIS.md. A fresh independently checked width9 invariant and actual symbolic CD8 traversals invalidate the tempting fixed-neighbor mode tags. Explicit old/new full-frame languages nevertheless remain disjoint, so no general deterministic-handler impossibility follows. Four proposed cooperative repairs are independently refuted by exact literal replay on a valid positive-CD8 interface frame. See COOPERATIVE27_COUNTEREXAMPLE_AUDIT.json: baseline600 steps to the required frame, versus152/24/154/154 steps to a wrong clean frame for the four repairs.

Audit conclusion: the baseline equality transport and these alternative source contracts have precise all-natural proofs; the recorded source certificates, literal repairs, selected symbolic frames, and concrete counterexamples were independently checked at their stated scopes. The complete baseline runtime is the separate encoding worker's replay, and the exact221 formal theorem is a documented inherited premise rather than a rebuild in this audit. No certified machine with at most218 states, exact219 kernel theorem, blanket compiler theorem, or state-count lower bound is claimed.

The final addendum independently accepts three infinite divergence certificates for further state27 actions. Exact prefixes and local rows were replayed; induction over the entire blank future half-tape establishes infinite extension, beyond finite observation. See COOPERATIVE27_DIVERGENCE_AUDIT.json and the final section of STATE27_ANALYSIS.md. Together with the encoding worker's separately reported834 concrete filter rejections, its final872-action family tally is837 interface-refuted and35 unknown. This audit independently verifies the three added certificates, not the entire834-case filter, and preserves all blank-run and global-calibration scope limits.
