# Source 54 — independent mathematical review

Reviewed on 2026-10-17 by the opening/encoder lane, separately from the intake owner's four-checker replay. Package root: `/tmp/zfc-intake-158/cachemp252_research_2026-10-17/cachemp252-research-20261017`. Declared source pin: `43026ff42f0939f09b9e95495248cfadcad38e38`.

**Verdict:** no mathematical blocker found in the stated cache-result MP source proof, the two alternative result-placement contracts, the independent shared-gate/NIP transformations, or the restricted NIP-macro obstruction. These are ordinary proofs with explicit scope; they do not themselves supply a new kernel theorem or a sub-252 machine. Two named ancillary diagnostic scripts are absent from the delivered tree. That is a reproducibility gap for those supplementary test counts, not a missing stage or failure in the complete four-stage default verification.

## Scope and procedure

I read the complete `report/cache_result_proof.tex`, `proofs/mp_success_interfaces.md`, and `proofs/nip_macro_obstruction.md`, plus the package README, default driver, source command checker, and the intake owner's replay record. I cross-checked the argument against the maintained `Enum254.lean`, `L2Control254.lean`, and `L2Lib254.lean` definitions and contracts. Main-report introductory claims were also read, but this dossier is the requested independent review of the three proof documents, not a second exhaustive audit of every experimental artifact.

No Lean/Coq/compiler/checker/version command, Python replay, dependency build, or repository edit was performed for this independent review. File enumeration and text inspection only were used. Package checksum manifests were not checked, in accordance with intake instructions. Reported finite counts below come from the owner's existing replay, not a new independent execution.

## 1. Cache-result MP proof

### Exact semantics and source change

`report/cache_result_proof.tex:20–45` changes successful MP from `(b,P(0,S),b,0)` to `(0,S,0,b)`, where `b=d+x` and the success test is `I(T,b)=H`, `I(a,b)=4P(a,b)`. Failure remains `(0,S,b,0)`. The only intended edit is the second child of source node 130, from 166 to 197. The warning against replacing every call of 166 is necessary: that helper remains used by other formula/parameter operations.

This follows from the actual helper interfaces. `L2Control254.lean:57–65` proves successful destructive comparison clears both its scratch operand and cache; `L2Lib254.lean:131–133` transfers current formula into scratch and clears the formula register; `L2Lib254.lean:126–128` unconditionally transfers the numeric parameter into the cache and clears the parameter. At the new success continuation, the comparison has already cleared the scratch and cache, so the transfer gives exactly the claimed result. It is not necessary to assume an initially zero cache: the initial cache is the implication premise.

The text correctly leaves transport of these helper run proofs to the edited DAG explicit (`cache_result_proof.tex:47–50`). Existing theorems about `dag254` do not automatically become theorems about the edited program.

### Soundness

The invariant `C254(T) ∧ C254(H) ∧ Good(S)` is preserved: on success, the old formula/cache premises derive `C254(b)` by the existing MP constructor; code 0 is a theorem; and the stack is unchanged. On failure, both formula fields become 0. AX, DROP, and NIP retain their original semantics, and NIP still halts only on incoming cache 1. Thus the proof introduces no new inference rule or axiom. This is the right invariant for the cache placement change.

### Uniform contract and completeness

The contract in `cache_result_proof.tex:79–86` matches maintained `Enum254.lean:435–436`: for every numeric initial top and stack, with numeric parameter/cache zero, a block either halts or returns `(X,S,0,0)`. It deliberately does not assume the input top or stack is already sound. This universal quantification is essential for persistent enumeration and the padded candidate argument.

The new MP block is

```
pA; DROP0; pI; NIP0; DROP0; NIP0; CMP(B); DROP0; NIP0.
```

Its complete trace at `cache_result_proof.tex:113–121` is correct. In particular the last DROP pushes zero but leaves the derived conclusion in cache; the last NIP removes that zero and clears the cache. The second NIP can halt if the premise A is 1, and the final NIP can halt if B is 1; both satisfy the contract. The unshifted Cantor convention, including `P(0,0)=0`, causes no exception because the inverse identity holds at zero too. A single DROP would not restore the contract; the text correctly avoids that shortcut.

The original discard block uses MP(1) only from cache/parameter zero, so its comparison must fail (`I(T,1)>0`). Its behavior therefore survives unchanged. The eight fixed axiom blocks and bundle block use discard and unchanged operations. The generalization block uses the supplied premise contract plus unchanged DROP/NIP/AX operations. These facts match `Enum254.lean:450–462`, `:581–613`, and the twelve-constructor induction at `:662–681`. Thus replacing only the MP induction case is sufficient at the ordinary mathematical level; no missing calculus constructor was found.

The cofinal argument in `cache_result_proof.tex:141–168` also addresses the right issue. Initial AX resets numeric parameter/cache regardless of working input; the subsequent uniform contract absorbs its arbitrary top/stack; the final three-command suffix halts when the block returns 1. The unused AX operand u makes the encoded candidate at least u. Choosing u at least the initial next-candidate counter avoids reliance on a candidate that has already been skipped. The source edit does not touch the proof-list pointer or next-candidate counter, so the old drain/reach argument remains available after interpreter transport.

For nine-register roots, only the unchanged fetch and first selector-read arguments may be reused directly after local transport. The explicit warning at `:170–176` is justified: stronger arbitrary-dirty reset results that inspected early old-MP cache outputs must be re-audited for the new output. The manuscript does not silently claim those stronger results transfer.

### Endpoint qualification

`cache_result_proof.tex:180–201` distinguishes the source-enumerator equivalence, binary/table/bootstrap/simulation obligations, external Lean endpoints, reconstruction in ZFC, internally serialized ZFC, and PA-internal certification. That separation is appropriate. This review does not promote the ordinary proof to a checked source theorem or infer the PA endpoint from a Lean theorem. The delivered positive machine has 252 working states; no sub-252 result follows from the shorter proof-block interface.

## 2. Alternative MP result placements

### Duplicated conclusion

`proofs/mp_success_interfaces.md:14–29` composes loops 198 and 207, yielding `(T,W,A,D,H,X,Y)=(b,S,0,0,b,0,0)` after a successful comparison. The maintained helpers at `L2Lib254.lean:162–166` and `:101–103` have precisely those copy/transfer effects. A new composition node is indeed needed even though both loops already exist.

The five-command normalization `DROP0; MP0; NIP0; DROP0; NIP0` has the stated trace at `mp_success_interfaces.md:50–56`. The delicate second step is sound: `I(b,0)=2b(b+1)=b` holds exactly for b=0. When b>0 the comparison fails and clears both formula fields; when b=0 the successful output is the same needed zero state. Final NIP may halt for b=1. Thus the modified MP block restores the same arbitrary-top/arbitrary-stack contract.

The separate measurement of a 253-state runtime and its affine results (`:31–37`) was not independently replayed here. The note correctly declines a blank-bootstrap claim for it. This variant is a valid source interface, not an improvement over the 252-state delivered machine.

### Conclusion in current formula and selector

The loop198/loop201 composition yields `(b,S,b,0,0,0,0)` in the seven displayed fields (`:80–97`), matching `L2Lib254.lean:86–88`. The selector is genuinely nonzero at this boundary and must be represented in the semantics; the note acknowledges this explicitly.

The encoded AX selector is added to the residual selector. Consequently nominal AX(0,b,0,0), entered with selector b, dispatches AX with actual selector c=b and first numeric parameter a=b. The freshness gate therefore clears the top. AX clears selector/parameter/cache and pushes its nine outputs plus the previous top b. Each of the nine outputs differs from 1 by constructor shape, as stated in maintained `Enum254.axList_ne_one` (`Enum254.lean:428–432`); this is stronger than sampling. Ten NIPs load b, then DROP0/NIP0 restore `(b,S,0,0,0)`, unless the final NIP halts for b=1. The thirteen-command suffix is correctly counted and does not require a negative operand or runtime choice.

The proposed cofinal extension for arbitrary initial nonnegative selector is sound in outline: adding encoded selector 3 always dispatches AX, which clears the selector; the initial AX output is absorbed by the uniform contract; the pointer still decreases and next-candidate counter is unchanged. A formal implementation must extend the boundary semantics and preserve those statements explicitly. No established binary budget is supplied for this variant.

### Transfer into the proof-list pointer

The rank observation at `:129–166` is correct under its stated semantics. At a non-fetch root the first decrement and two Cantor unpairings give `r+x<L_old`, using `P(a,b)≥a+b`. Thus after operand accumulation, `r+(D_old+x)<L_old+D_old`. Moving all of D into L preserves that sum, so `L+D` decreases even though L alone need not. AX consumes further pointer data and clears D. Next-candidate counter preservation is essential.

This proves drain/termination between fetches, not completeness. The document appropriately leaves the numerical continuation compiler, sentinel convention, and padding argument as further work. Packing residual pointer `K-b` only makes sense after ensuring `K≥b` and respecting the decrement convention. It supplies no license to add b to nextproof, which could skip candidates. This is a useful new search direction, but no implementation or full compiler proof is claimed.

## 3. Shared gate and specialized NIP

### Hoisted successful transfer

The edits at `mp_success_interfaces.md:213–217` are consistent with the structured break semantics. Changing helper129's failure to Break2 lets node130's left-child context reduce it to Break1, so node130 can itself serve as a condition: equality executes transfer197 and returns normally; inequality clears scratch/cache, preserves D, and returns Break1 to the outer gate.

The AX-tail calculation at `:229–237` accounts for the significant side effect. At the first gate, equality moves a early into H and clears D; inequality leaves D=a and H=0. After restore211 and the existing transfer197, both cases have `X=c,Y=0,D=0,H=a`; the current formula has the proper first mask. The second gate sees D=0, so its new transfer is harmless and it applies the original second mask. MP enters with T=0, making the added top clear harmless. NIP failure retains its pop behavior; success can change D immediately before halt without changing whether it halts.

No source node is added, and the retained left/right contexts are a plausible compilation advantage. That does not establish a state saving. The earlier direct common-action construction's lost context bit is a substantive warning, not a contradiction of the register algebra.

### Specialized NIP zero/one test

The independent edits at `:255–257` preserve helper129's original Break1 convention. Helper128 returns normally on cache zero and otherwise clears it and returns Break1. The three original-cache cases are correct: H=0 causes the first decrement to fail and proceeds to pop; H=1 reaches zero and then halts; H≥2 is cleared by helper128, whose break skips the halt, then pop occurs. This gives exactly the old NIP boundary semantics from clean scratch states without using X.

The two transformations are expressly separate. They must not be combined verbatim: the hoisted gate changes helper129 to Break2, while specialized NIP relies on its original Break1 behavior. Any combined candidate needs a new control-flow argument and exact compiled evidence.

## 4. Restricted impossibility of replacing NIP

`proofs/nip_macro_obstruction.md` proves a correct, appropriately restricted statement. For fixed operands, each permitted MP, DROP, or AX command preserves agreement on observable fields `(T,d,H)` independently of the initial stack. Neither original MP nor cache-result MP reads a pre-existing stack entry into those fields at its command boundary; DROP/AX only push. Induction gives the same property for every fixed finite macro of these commands.

Both witness states `(0,0,0,0)` and `(0,3,0,0)` are Safe: 0 is a theorem; `3=P(2,0)` and code 2 is the universal closure of theorem 0. NIP(0) does not halt on either state but returns cache 0 versus cache 2. This contradicts the macro's stack-independent observable output. Internal temporary unpairing inside an implementation does not evade its specified net boundary semantics.

This is not a Turing-machine state lower bound and does not exclude changing a primitive to read the stack, changing representation or interface, or choosing a different proof-search algorithm. The report states these limits clearly. The result is useful for ruling out one overly narrow opcode-elimination search, rather than for stopping broader minimization.

## 5. Missing ancillary scripts versus complete default verification

A recursive `rg --files` enumeration of the entire delivered source54 tree finds neither `mp_success_interfaces.py` nor `shared_gate_and_nip.py`. Recursive content search over Python, Markdown, TeX and the packaged-files inventory finds their names only in `proofs/mp_success_interfaces.md:190` and `:276` respectively. No alternate implementation of those exact described source-diagnostic suites was identified.

Accordingly, the following counts are documentary historical claims and were not reproduced from the delivery:

- `mp_success_interfaces.py`: 141 literal full-MP cases per alternative variant, 330 duplicated-result normalizations, 1,200 duplicated-MP contract tails, 108 selector normalizations, largest conclusion 4,097 bits (`:190–198`).
- `shared_gate_and_nip.py`: per independent transformation, 141 complete MP cases, 90 NIP cases, 256 complete AX-tail cases (`:276–282`).

The tree does contain other related scripts and artifacts, including duplicated-result binary/decoder records, `hoisted_gate252.py` and results, `role_aware_compiler252.py` and specialized-NIP artifacts. Their presence is not the missing named suites; conversely, it would be inaccurate to say that all supplementary experimental evidence is absent.

The default `verify.py:40–44` explicitly invokes exactly these four existing jobs:

1. `machine/verify_bootstrap.py`;
2. `checks/verify_source.py`;
3. `source-binding/verify_source_binding.py`;
4. `checks/verify_affine.py`.

It does not invoke either absent script. The delivered `checks/verify_source.py` covers the central cache-only source edit, transfer, contract tails and exact repair; it does not implement the described duplicated/selector/shared-gate ancillary suites. Thus the gap concerns supplementary reproducibility and should not be recast as a default-driver failure. Recommended intake treatment: preserve delivered bytes, annotate those two diagnostic claims as unreproduced/missing scripts, retain the ordinary proofs with their stated scope, and retain the actual default PASS separately.

## 6. Existing replay record inspected

I read `/tmp/zfc-intake-158/run54/result.json`. It records the owner's command `/home/codex/.local/bin/python -B /tmp/zfc-intake-158/run54/replay.py`, exit 0, elapsed 12.8144040685 seconds. Only manifest verification was bypassed in memory per intake; the exact one-edge source-edit test and all four substantive stages remained. Recorded results:

- 252 working states, 504 rows, 707,393 blank steps in each of two independent literal replays; 55 support rows unchanged.
- Source binding: 2,998 entries, 2,997 decrement sites plus one halt, 5,995 branches including the initial branch, maximum segment length five; all nine register effects and both decrement outcomes checked. Eight hundred branches differ in increment order while agreeing in counts; 16 increment vectors; pointer codes fit the 128-bit decoder.
- Source commands: 588 old/changed full-MP cases, 128 helper197 cases, 3,600 full contract tails and 1,056 exact six-command repairs; largest formula parameter 4,097 bits.
- 8,361 affine cases, minimum literal progress 13.

These are observed records from the owner's bounded run, not a second execution or a proof of the unbounded theorem by sampling. No new checker or proof-assistant run was performed by this reviewer.

## Useful consequences for the current task

The strongest reusable idea is that the old MP result placement is a compiler interface, not a logical necessity. The cache-only result has a short exact normalization and a uniform completeness contract. Alternative placements can therefore be evaluated against physical register/control costs while keeping the logical calculus fixed. The proof-list rank `L+D` gives another legitimate degree of freedom, but needs a continuation compiler. The shared-gate study shows why source simplification must preserve the binary compiler's context information. The NIP obstruction focuses future opcode work on adding a stack-read effect or changing representation, instead of searching impossible fixed macros under unchanged semantics.

None of these observations alone beats the current 252-state count or closes the PA-internal endpoint. They are concrete candidates for further minimization and proof engineering, supported by ordinary arguments with clearly separated remaining implementation and certification obligations.
