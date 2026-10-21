# Proof-oriented comparison of K215, ZC215, ST215, FT215 and GC215

## Recommendation

For the least new formal verification, keep the already certified K215 table and factor its proof. Its initialized numerical stack is zero, so every decoded head is truth and ordinary theorem-valued-store preservation suffices: it needs neither a protected-tail debt bound nor ZC's injection. A new candidate cannot be called easier merely because it has fewer primitive leaves or runtime cases.

Among the reviewed *alternative* 215-state constructions, ZC215 is the strongest candidate for a clean independent formalization. Its startup lands at a genuine command root with an arbitrary opaque stack tail, its four-command compiler is unchanged, and a single structural injection replaces density estimates, numerical cutoffs, AX startup-prefix matching and reserve accounting. This is a qualitative estimate, not a measured Lean/Rocq code-size result. It does not assert that ZC's complete proof beats a refactored K215.

GC215 improves only one local completeness block relative to ST215. It drops J(i) from generalization by using the private AX command tag as binder. It retains ST's indirect stack macros, initial synthetic AX-prefix bridge, conservative debt-two proof and cofinal enumeration proof, and adds a contextual decoder merge. FT215 introduces a forced transfer before every candidate and has exact debt seven; that is a semantic novelty, but not a proof simplification.

## Comparative obligations

- **K215 (compiled endpoint)**: four commands DROP/NIP/MP/AX; zero numerical stack at initialization; cofinal compiler handles initial cutoff four; already proved numerical calculus, source interfaces, runtime and endpoint can be reused. Exact table proof exists in both systems according to supplied upstream record. No local compilation was undertaken in this comparison.
- **ZC215**: same four-command contracts and full axiom/formula encoding; exhaustive raw candidates 0,1,...; NIP-to-DROP tag lowering proves no opaque-tail exposure; exact root startup requires no partial-AX logical bridge. Same strong compiler works. Since enumeration starts at zero, one encoded successful word suffices and a cofinal padding argument can be omitted from the endpoint dependency. It still needs proof that every candidate drains and source refill really enumerates those integers. All-natural runtime has 6,177 cases in supplied evidence, not a new kernel endpoint.
- **ST215**: three commands S/MP/AX; S removes old DROP/NIP interface; derived H and PUSH macros restore structural functionality. Startup is a prefix of synthetic AX(0;0,0) above opaque tail 2. Ten safe heads and debt two are substantive: the tail contains buried falsity. 6,151 cases in supplied evidence, ordinary proof only.
- **FT215**: same three-command compiler with forcing-compatible completion/fairness; schedule S;W(0);S;W(1);...; debt seven requires recursive Cantor-diagonal counting, a uniform large-index bound and exact finite base. Ten initial heads leave margin three. 6,152 cases. These additional scheduler obligations make it an unlikely shortest-proof choice.
- **GC215**: same three-command structure as ST. Only ninth AX output changes Q_U(oldH) to Q_C(oldH), preserving every axiom, gate and dominated-row parameter. GEN removes J(i); H/PUSH proofs use tag and position, not binder. Existing source CFG unchanged but two arithmetic register operands differ. Physical merge of roles 129/310 adds a marker-sensitive local correctness obligation. 6,151 cases claimed in packet. No exact-table kernel endpoint.

No candidate here changes the inherited consistency comparison of the numerical calculus with ZFC. In particular GC's supplementary restricted sixth-axiom theorem is not used by GC215 and should not be pulled into its proof dependency graph.

## Concrete reusable proof architecture

1. Define a single raw-natural numerical calculus, with truth/falsity and all aliases explicit. Prove its ZFC-refutation calibration once. Do not introduce a well-formed-formula premise that actual machine candidates do not satisfy.
2. Parameterize AX's GEN output by a binder selector beta(U,C), requiring only that it is a natural binder and that the compiler can choose the requested value. Instantiate beta=U or beta=C. Keep other AX rows literal. Do not rebuild the underlying calculus for GC.
3. Prove command contracts once. Package safe-store preservation separately from strong completeness blocks. Soundness starts from theorem-valued stores; completeness must allow arbitrary incoming top and stack and may stop at an earlier halt. Conflating these contracts leads to false proofs.
4. Package raw wire parsing: encode/decode identity, positive-continuation strict descent, field arity and candidate draining. Prove a generic enumeration theorem, then choose exhaustive or cutoff/cofinal coverage. This replaces repeated arithmetic-control arguments, not the required source-return audit.
5. For zero-stack K use a coinductive/numerical all-heads predicate. For arbitrary-tail candidates use a finite theorem-head wrapper above fixed opaque tail. Expose a generic balance/safety theorem whose scheduler supplies a prefixwise credit inequality. ZC instantiates it using the injective occurrence map; ST/FT use their existing bounds. Do not force the simpler K instance through protected-tail arithmetic.
6. Formalize the primitive symbolic certificate checker once in Lean and Rocq, prove its interpretation sound, and check machine-specific certificates by kernel reduction or proof-producing reflection. Certificates and reconstruction programs are untrusted data; the checker theorem, exact table/source interpretation and final kernel proof are the trust boundary. Positivity and termination of every simulated block must be recorded. A Python PASS is not that kernel proof.
7. Verify finite complete startup by computation and use a generic frame theorem. Start-state, whole finite tape plus zero exterior, dispatcher, registers, source ordinal and scratch/spare conditions all matter. For ST/FT/GC additionally prove the partial-AX source bridge. Do not infer a command-root state from a plausible register tuple.
8. Compose one generic endpoint: exact startup + positive-duration bidirectional halting simulation + source soundness/completeness + numerical calibration. Preserve the distinction between an external equivalence theorem and an internal PA theorem; refactoring cannot supply a missing arithmetization theorem.

The compact result should consist of definitions, shared soundness lemmas, a small exact candidate record and computational proof terms. Aim to reduce duplicated theorem statements and proof infrastructure rather than merely hiding megabytes of generated code behind imports.

## ZC injection in its shortest reusable form

Encode each nonempty command word by nested strictly coordinate-monotone pairing, inserting successor only on nonempty continuations. An occurrence is (candidate number, command position). Replace a NIP tag 1 by the same-arity DROP tag 0, leaving every field and other command unchanged. The encoded candidate strictly decreases; changing that same occurrence back is an inverse on the image, so the map is injective. Therefore every NIP in an executed finite prefix has a distinct DROP in an earlier completed candidate. Immediately before any NIP there is one unmatched safe push. This proves prefix safety, not just final balance, and requires no credit from AX.

Necessary hypotheses: unique parsing/encoding, strict coordinate monotonicity, same arity, exhaustive increasing enumeration beginning at zero, and no skipped candidate or altered source return. Removing any of these requires a fresh theorem. The rejected SB215 source is not rescued by such an abstract scheduler proof.

## New independent checks and limits

GC ZIP was copied from Library ID libfile_73d40a278d3881918bb2b7f2f141044b and safely extracted as data, rejecting parent paths and symlinks. No received script was run. A locally written literal simulator independently confirmed 430 rows / 215 working states and ran both native and dense tables for 68,710 blank transitions; both reached the expected dispatcher at head -2 with identical complete 100-one-cell tapes. See GC_LITERAL_REPLAY.json and check_gc_data.py. This does not revalidate register decoding, source/AX bridge, all-natural runtime or logical calibration. Supplied runtime receipts are evidence claims, not independently rerun proofs here.

## 214-state implications

None of these proof simplifications constructs a 214-state table. Command-count, primitive-leaf count and distinct-source-subtree count are not physical-state counts. A prospective ZC + command-tag GEN hybrid may be worth testing, but its changed source-role allocation and startup/runtime must be rebuilt before assigning even a 215-state count. It would add a new binder instance for only a small compiler saving, so it is not recommended over proof refactoring without a concrete allocation gain.

## Source locations

K: research215_round6_rho6/upstream/ZC215_Research_2026-10-21/reference/k215-proof.md and command-compiler.md.
ZC: same package, proofs/tag_lowering_credit.md and README.md.
ST: research215_round4_source/upstream/direct-transfer__README.md; research215_round4_report/package/proofs/inherited_short_transfer_compiler.md.
FT: research215_round4_report/package/proofs/FORCED_TRANSFER_CREDIT_THEOREM.md and FORCED_TRANSFER_CALIBRATION.md.
GC: gc_inert/ZFC_GC215_2026-10-21/README.md, proofs/generalization_binder_c.md, evidence/decoder-merge.json.

## Addendum: proposed zero-debt / command-tag-GEN hybrid

A hybrid combining ZC's four-command zero-debt scheduler with beta(U,C)=C is semantically coherent, conditional on an exact source/table realization. Its GEN block is

    B_X; DROP; NIP; AX(i;0,0); NIP^9; DROP; NIP; NIP.

Starting from the strong block result (X,w,0,0), DROP/NIP yield (0,w,0,X). AX's ninth head is Q_i(X), tenth is saved zero. Nine NIPs put Q_i(X) in cache; DROP moves it into top while saving AX's current top; the last two NIPs restore stack w and zero cache.

There is a nontrivial qualification: AX's gate is now G(0,X,i), not necessarily zero. The final NIP tests that saved gate. It must be proved nonfalsity (zero when disabled, implication-coded when enabled). In the original four-command GEN block, J(i) arranged U=A=C=i and the gate was identically zero. Thus deleting J(i) removes a command but adds a use of the full gate's nonfalsity theorem. Soundness uses unrestricted theorem-only GEN for binder C; other AX rows and dominated inequality U<=A are unchanged.

Tag lowering and exhaustive fairness are unaffected if all field arities, continuation rules and actual scheduler returns remain unchanged. No old compiler proof should be reused by textual substitution alone: check where the original proof used gate zero rather than merely a nonfalsity/tag fact.

Relative to a refactored certified K215, the hybrid still introduces a new protected-tail injection, modified GEN contract and proof, exact source/runtime binding and a possible marker-sensitive conditional decoder fold. It is not presently justified to claim a shorter complete kernel proof. It may yield a cleaner pedagogical abstract machine, while K215 remains the lowest-risk route to shorter certified proof code.

A separately reported generic Lean symmetry refactor is much stronger evidence of an actual simplification than the hybrid's one-command saving: reportedly a 63-line generic equivalence lemma removes 2,240 reversed checks across 16 files. Historical summed compilation cost of those files is not a measured speedup of a rebuilt project; report any timing only with that distinction.
