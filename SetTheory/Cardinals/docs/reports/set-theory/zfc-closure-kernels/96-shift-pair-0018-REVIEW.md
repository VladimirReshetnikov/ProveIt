# Independent shifted-pairing review

## Verdict and scope

**QUALIFIED PASS.** No concrete mathematical defect was found in the proposed abstract transfer for `E(a,b)=2^a(2b+1)-1`. The generic theorem uses both inverse laws, `p(0,0)=0`, and both field bounds. Effective conclusions additionally need computable `p,u`; the primitive-recursive conclusions need primitive-recursive `p,u`. The reviewed report explicitly states these qualifications, and the concrete shifted functions satisfy them.

The accepted mathematical scope is:

1. The numerical calculus retains its exact ordinary native first-order refutation theory, via models and fresh matrices, rather than a direct numerical proof-code isomorphism
2. Finite proof certificates, their parser, the command coding, and both halting directions of the **abstract enumerator** transfer
3. The actual logical seed `(3,0,0,0,3,0,0,0,0)` satisfies the required invariant; no assumption of a zero additive parameter or a zero next-proof counter is needed
4. Independently reconstructed source data has the claimed replacement-only structure and clean helper-entry invariant. The actual helper CFGs satisfy the clean arithmetic contracts by the loop arguments below

This is mathematical review and a self-authored executable audit, **not a new kernel-checked development**. The final ZFC endpoint composes the separately inherited NativeAx/SIR/ZFC comparison; this review does not re-prove that comparison's internal Foundation or constructible Choice argument. In particular, the old NativeTheory source by itself does not certify the entire ZFC endpoint.

There is no emitted shifted literal binary table, state-count improvement, new blank bootstrap, whole-frame runtime certificate, or established source-to-literal-machine theorem. The changed source needs its own exact source/enumerator composition and downstream compilation/runtime proof. The old Cantor numerical calibration cannot be reused as an equality bisimulation.

## Theory checks

### Pairing, zero, and recursion

Unique factorization of `n+1` proves both inverse identities. The inequality `E(a,b)>=a+b` follows from `2^a>=a+1`; equality occurs only at `(0,0),(1,0)`. In particular, a universal strict first-field bound would be false. The report correctly allows `E(1,0)=1` and instead uses the formula tag division and command-list successor delimiter wherever strict decrease is required.

Every positive formula code has recursively decoded children at most `floor(n/4)<n`. Actual named formula encodings are positive. Code zero is an intentional tautology alias, not the image of an actual finite named formula. The special implication case `I(0,0)=0` preserves semantic implication because both relevant readings are tautologies.

The occurring-label proof uses only field bounds and positive tags. The zero decoder does have a syntactically free label zero, so syntactic freshness at zero is false. The report uses the correct semantic replacement: the decoded zero tautology is invariant under every valuation. This gives uniform own-code semantic freshness, including after other variable updates.

### Native theory and the unsafe direct map

I compared the claimed transfer with the supplied native adapter definitions as text. The full equality-inclusive actual-formula GIC schema, genuine bottom, nonempty-domain witness, and both directions of the decoded/encodable model bridge are preserved.

The `a=b` branch cannot be discarded. Its container forward condition is vacuous by irreflexivity, and the bottom-matrix GIC instance supplies the required empty image. For distinct `a,b`, the gate and semantic own-code freshness give the decoded matrix adapter.

In the reverse direction, hygienic odd free names/even binder names and relative falsity are valid under global irreflexivity, including binder zero. Padding `((f->f)->f)` preserves classical truth, has encoded code greater than 3, and cannot contain its own encoding as a label. The new bundle at names `1,3,c` therefore meets both gate inequalities and yields the requested actual native matrix instance with all parameters.

The report correctly rejects the naive recoding map: old `R(1,1)=17`, shifted `R(1,1)=21`, and the old passing parameters `(21,22,17)` become a gate failure if only the formula code is changed to 21. Preserving the original binder instead does not give the new bundle's required own-code binder. The fresh-matrix proof avoids both mistakes.

The translation from the relative-falsity proof calculus uses the exact existing eight rows, MP, GEN and projected atomic vacuity. Inspection of the original `c254_of_thmG` and completeness proof revealed no extra Cantor-specific arithmetic premise beyond the generic interface. K/S/Peirce are polymorphic in implication, and row 6 gives explosion. The translated IR identity is already derivable. Its shifted code 162 is not a newly added ordinary axiom or a deleted row.

### Effective certificates and both halting directions

The twelve raw-proof constructors are unchanged. Successor/base-12 node coding makes every recursive proof child strictly smaller than its enclosing code, including the payload-zero cases. For computable pairing this gives a decidable finite certificate predicate; for the concrete primitive-recursive pairing, bounded parsing and validation are primitive recursive. The search translator between refutations is only guaranteed to terminate on valid refutations. No direct primitive-recursive numerical recoder was established or needed.

The theorem stack uses raw pairs, whereas command-list suffixes use successors. These conventions must remain distinct. A positive command pointer decreases because its inverse residual is bounded by `pl-1`; no strict generic inverse-tail bound is assumed. Thus each candidate drains unless it already halts.

I checked the block identities in the report against the exact command semantics:

- Discard produces clean zero only from the stated `d=h=0` entry interface
- AX pushes ten entries: old current formula, GEN, and eight rows
- Ten NIPs restore the underlying stack; the row-selection counts and both GEN/MP cleanup blocks restore the claimed clean interface or halt earlier
- Every logical row and bundle has tag zero, and GEN has tag two, so none of these cleanup entries equals target 1
- The reset prefix AX accepts arbitrary incoming working registers and leaves the clean interface required by Build
- The padded candidate code is at least its free parameter by repeated field bounds, making successful proof witnesses cofinal even when the next candidate is initially 3

Soundness needs `C_p(t),C_p(h),Good_p(S)`. Completeness works from every six-register state because the reset and candidate-draining argument require no initial logical invariant. The displayed nine-register seed maps to `(pl,np,t,S,d,h)=(0,3,0,0,3,0)`, so soundness also applies. Both abstract halting directions follow.

## Independent data/implementation checks

`check.py` imports only the standard library and treats the original Coq DAG and companion JSON as data. It does not import or execute the downloaded code or either companion checker. It builds its own control-flow graph by continuation stacks, independently of the companion's path-suffix routing algorithm.

It reconstructs the original 219-node DAG and verifies exactly 6460 leaves. Replacing only original nodes 115, 116, and 162 with the supplied inverse-L, inverse-W, and pairing trees reproduces **both** serialized changed sources exactly. Their independently counted sizes are:

- Initial shifted source: 7788 leaves, 234 distinct binary DAG nodes
- Best supplied shifted shape: 7788 leaves, 232 distinct binary DAG nodes

Both whole-source zero/positive fixed points contain 625868 abstract states and 362 helper occurrences. Every external inverse entry has `X=Y=0`; every external pairing entry has `Y=0`. Positive decrements have both zero and positive successors, so this is an inductive overapproximation, not a bounded concrete trace. Initial support is exactly registers N and D; arbitrary magnitudes with that support are included. The result is a reachable-entry invariant, not a dirty-scratch contract for arbitrary entries.

The helper CFG interpreter independently checks 135 pair entries and 4097 inverse inputs for each of L and W in each variant: 16658 finite helper executions, with every untouched register checked. Separate pairing tests cover 65536 inverse inputs and 8481 forward pairs. All pass.

### Unbounded clean helper contracts bound to exact CFGs

The script also compares every helper's normalized CFG against explicit literal normal forms. Both variants have the same arithmetic CFG; only the resolved structural jump-depth spelling differs. `helper_cfgs.json` retains these graphs.

For Pair, PCs 0–3 transfer T to Y twice, leaving `T=0,Y=2b`. At PC 4 each positive X is decremented once; PCs 5–8 double Y into T, PCs 9–11 transfer T back to Y, and PC 12 increments Y. Thus each outer iteration sends `y` to `2y+1`. After exactly a outer iterations, `X=T=0,Y=2^a(2b+1)-1`. Each transfer loop has its source register as a decreasing rank, and the outer loop has X. Only X,T,Y are written.

For either inverse, PCs 0–5 remove two source units and increment Y, until the source is exhausted. Exhaustion on the first test means an even remaining input and exits with its half in Y. Exhaustion on the second test means an odd remaining input `2b+1`; PC 6 increments X, PCs 7–9 transfer the half b from Y back to the source, and PC 10 restarts. At each outer restart,

`original n + 1 = 2^X * (current input + 1)`.

Odd restarts strictly decrease their positive current input; the inner halving and transfer loops also terminate. The final even input is `2Y`, giving `n+1=2^X(2Y+1)`. Uniqueness proves the exact inverse fields, with the source cleared. Only the source,X,Y registers are written. The zero case exits immediately with both fields zero. These arguments establish total finite clean helper return for all natural inputs and preserve all other registers.

## Required limits on publication

It is accurate to report a qualified abstract pairing/calculus/enumerator transfer, independently checked source replacement and clean helper contracts, and a **worse** measured source DAG cost for these particular implementations. It is inaccurate to report a smaller binary machine, a new <245 result, a transferred old table certificate, or a new kernel build. The 232-node source result is not a lower bound on other pairing implementations.

All source and report identities used by this audit are recorded in `checks.json`. This directory is separate from the already sealed continuation audit and its main report.
