# Delayed-erasure transfer from boundary239 to combined238

## Result and scope

The delayed-erasure reduction is a parametric local theorem. It is not tied to the original rotation240 source tree or the other decoder rows. It applies to the boundary239 table once its one semantic selector guard has been established for that table's blank run. The incoming-port predicates and the six whole-tape block identities transfer literally to boundary239. A fresh complete symbolic audit establishes the guard; the previously packaged rotation240 guard receipt is not used as evidence about the changed source.

This note describes an ordinary mathematical proof formalizable in ZFC. It is not a new serialized Lean/Rocq theorem. The already-established source calibration is an explicit inherited mathematical dependency.

## Exact tables and edits

The old machine B is boundary239 with inherited labels, start95, dispatcher96 and halt254:

- SHA-256: d061770f487937f9da652919c9bc9bb79bc9bf137ca41dd7a08eb5ecda8e7719
- 239 working states and 478 transition rows

The new machine N has inherited-label SHA-256:

069942be27db9736875ea042320e51ac3b1eac7116cbe01cdce520fa6056f78c

Apply exactly these three changes to B, then delete both rows of169:

- 147/0: (0,R,169) becomes (0,R,80)
- 80/0: (0,R,25) becomes (0,L,106)
- 91/1: (0,L,50) becomes (1,L,167)

The only incoming edge to169 in B is147/0. The resulting machine has238 working states,476 rows and a single separate halt254. Let φ(169)=80 and φ(q)=q otherwise. Configuration correspondence preserves head and the complete tape and applies φ only to control.

## Parametric theorem

Let B be any deterministic complete binary tape machine with initial control95 and designated halt254. Let N be exactly the patched machine just described. Assume:

1. Every incoming row of B preserves the four predicates below, and the initial configuration satisfies them.
2. The six finite block identities below hold in the literal tables for every tape satisfying their assumptions.
3. Every B configuration reachable from the initial configuration satisfies the semantic guard q=169 and T(h)=1 ⇒ T(h+1)=1.
4. Other rows correspond under φ, and no displayed block passes through halt prematurely.

Then B halts from its initial configuration if and only if N halts from the corresponding configuration. No other constraint on unaffected rows is needed, except their preservation of the invariants and semantic guard.

### Structural predicates

- q67 implies T(h−1)=0
- q80 implies T(h−2)=0 and T(h−1)=1
- q91 implies T(h−3)=0 and T(h−2)=T(h−1)=1
- q169 implies T(h−1)=0

For actual B, the complete incoming sets are:

- q67:52/0 and124/0, both write0 and moveR
- q80:67/1, which writes1 and movesR
- q91:80/1, which writes1 and movesR
- q169:147/0, which writes0 and movesR

The initial state95 is distinct from all four. Induction on ordinary machine steps proves these predicates even for an arbitrary starting tape. In contrast, the selector guard in hypothesis3 is a representation invariant, not an arbitrary-tape fact.

### Six exact block identities

Each row starts with the same tape and head h on both sides, with new control φ(q). The endpoint has equal control, head and complete tape. Any cell not explicitly assumed remains an independent arbitrary bit; its value is neither guessed nor sampled.

| Old control/read | Additional facts | Old steps | New steps | Common control/head |
|---|---|---:|---:|---|
| 80/0 | T(h−1)=1 | 1 | 5 |25,h+1|
| 80/1 | none | 1 | 1 |91,h+1|
| 169/0 | T(h−1)=0 | 1 | 3 |57,h+1|
| 169/1 | T(h−1)=0; T(h+1)=1 | 1 | 5 |56,h+1|
| 91/0 | none | 1 | 1 |106,h+1|
| 91/1 | T[h−3,h)=011 | 3 | 11 |2,h−3|

The new nontrivial paths are:

- 80/0:80→106→92→107→125→25
- 169/0:80→106→93→57
- 169/1:80→91→167→151→173→56
- 91/1:91→167→151→24→36→54→71→82→94→50→20→2

The old path for91/1 is91→50→20→2. Both paths erase precisely the three initial1s at h,h−1,h−2. The selector169/1 pair erases precisely cell h. Other comparisons preserve the tape. The independent local verifier checks all these claims directly, rejects an unconstrained read and compares the entire finite modification maps with unchanged arbitrary exterior cells.

### Positive-block proof

Start at the common blank configuration. At any paired checkpoint whose old state is not80,91 or169, use one corresponding transition. In particular147/0 is covered by mapping its target through φ. At a special checkpoint choose its unique row of the six-case table. The old predicates and guard provide all required tape facts, and the block endpoints are again paired.

Each old block has length1 or3 and each new block has positive length at most11. The explicitly traced old and new blocks contain no premature halt. Thus an old finite halting run partitions into finitely many whole blocks and induces a new halting run. An infinite old run has arbitrarily many blocks; their positive new lengths produce an infinite new run. Determinism and completeness then give the reverse implication as well. No separate invariant for arbitrary intermediate new configurations is needed: predicates are used only on old reachable configurations at checkpoints.

For any complete finite run, the time difference is

4 n(80/0)+2 n(169/0)+4 n(169/1)+8 n(91/1),

where counts refer to the old run. The three-step old91/1 block contains neither another91/1 nor another weighted row. Consequently the count formula is literal. Every block has duration ratio between1 and5.

## The fresh boundary guard proof

The guard audit uses boundary239 and its exact source digest7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6. It checks:

1. Every concrete state169 visit in the409691-step old blank initialization. The complete endpoint is independently compared with the calibrated frame: state96, head−5, extra gap117, nine logical values(3,0,0,0,3,0,0,0,0),167 spare values1 and exactly351 one-cells; all other cells are0.
2. Every state169 visit during all8386 guarded instruction proofs, ranging over all natural primary register values, arbitrary extra gap, arbitrary first spare and arbitrary finite spare tail.
3. At any q169/read1 event, the head orientation is rightward and the current right1-run has affine length with nonnegative coefficients and constant term at least2. Thus its next physical tape cell is1 for every represented valuation.
4. No q169 control can be hidden by a symbolic acceleration. Its rows are not self-loops; all four exact one-block finite-list schemas are rederived and their entire literal/unary traces exclude169. Their empty-list base cases take no steps. No list schema has entry169, and the wrapper rejects any opaque/list source at169.

The symbolic engine's only motion rules are literal transitions, self-loop unary induction and the four rederived finite-list inductions. Word normalization uses the finite-list identity C(A)1=1B(A), with B(v)=01^(v+1), C(v)=101^v, and its reversal. The generic register values are independent nonnegative integers. The4000 limit bounds proof-construction steps, not any represented register value, tape length or actual runtime.

The fresh completed audit returns BOUNDARY239_UNBOUNDED_SELECTOR_GUARD_PASS: all8386 cases,2247513 symbolic rules,96 symbolic state169 visits, and32 positive169 events. Every positive event is an increment of logical register4, and its right1-run is G+K with23≤K≤59. Startup has18 state169 visits, of which6 read1. Thus the changed boundary source has been checked independently; the original guard's lower margin21 was not simply transferred.

Because startup reaches the calibrated frame and each complete instruction interface restores another such frame with positive time and a nonempty spare suffix, induction over source instructions covers the entire subsequent blank run. Source successor/path normalization must be preserved; the independent boundary source audit supplies that interface, including the empty initial path. This gives hypothesis3 and therefore the local transfer.

## Logical composition

Let P0 be the calibrated rotation240 register source, P1 the boundary source, and R* the nine-register seed above. The exact claims compose as follows:

Halt(N,blank) ↔ Halt(B,blank)
↔ RegisterHalts(P1,(empty,R*))
↔ RegisterHalts(P0,(empty,R*))
↔ BProv(ZFCax_s,[],false)
↔ there exists a finite ZFC proof of contradiction.

The first equivalence is the theorem above. The second uses old B's exact startup and universal runtime interface; the combined238 direct runtime replay is an independent alternative to the first two steps. The third is the boundary source-rotation equivalence for every register file, including successor canonicality. The fourth is the explicit inherited theorem CalibratedRotation240.halts_iff_zfc_refutation. The fifth encodes and decodes finite derivation trees by structural recursion, or translates between conventional effective proof codings.

The physical spare suffix is auxiliary storage, not the logical registers beyond8: the source uses only register operands0 through8. The source's higher logical registers remain irrelevant, and the fixed seed's higher logical values are0.

All new proofs here use finite syntactic checks, natural-number induction and finite-list induction; ordinary ZFC can formalize them. This composition neither assumes Con(ZFC) nor appeals to general soundness of Lean inside ZFC. It inherits the actual prior calibration mathematics (enumerator correctness and the native-calculus/ZF/ZFC refutation comparisons), not merely an informal equiconsistency slogan. Negating the halting equivalence gives the requested ZFC theorem Nonhalt(N) ↔ Con(ZFC). It does not establish unconditional nonhalting. Bare consistency alone is not asserted to give two-sided independence.

## Reproduction and trust boundary

- audit_local_transfer.py produces local_transfer.json and deliberately uses explicit errors, so its finite checks survive Python -O.
- audit_boundary_guard.py produces boundary_guard.json. Its imported symbolic engine requires assertions enabled and rejects optimized Python.
- The local finite verifier does not import the original delayed-erasure certificate or any runtime engine.
- The unbounded guard checker independently strengthens the event/non-hiding instrumentation but reuses the audited universal symbolic execution engine. This is not a separately implemented proof kernel.
- The independent boundary source audit is in ../boundary_audit/independent_boundary_audit.json.

Read fresh receipt statuses and hashes, not process exit alone. The source calibration and source-transformation proof remain separate explicit dependencies of the final consistency theorem.

## Additional independent consistency checks

The literal blank runs were also aligned block by block, comparing their complete tapes at all409685 checkpoints. This independently confirms409691 old steps versus409835 new steps and the precise weighted counts(18,12,6,3); see boot_blocks.json and audit_boot_blocks.py.

Comparing the two complete runtime case receipts gives identical affine head motion in every case. Of8386 guarded cases,7628 have unchanged duration,274 gain8 actual steps and484 gain12 actual steps, independently of every symbolic register/gap/spare parameter. The coefficientwise bounds t_old≤t_new≤5t_old hold throughout; see runtime_clock_comparison.json. This comparison is corroboration, not a substitute for the fresh local or unbounded guard proof.
