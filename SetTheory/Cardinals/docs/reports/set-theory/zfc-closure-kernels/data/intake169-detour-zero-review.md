# Detour242 and zero-branch reuse: independent static comparison

Both main machines are the already known primary 242A construction. Detour's inherited table is byte-identical to 242A. Zero-branch's entire 484-action table is 242A after renaming its retained state 15 to 27. Neither supplies another independent deletion on the present 241-state machine. Both reports should nevertheless be retained for their distinct equational-front-end work.

This review reads the ordinary proofs, transformation code and serialized terms as source/data. It does not execute delivered programs, simulators, guards, proof compilers or consistency searches. The accompanying own static parser reconstructed all three advertised packet bitstrings exactly and checked the full table isomorphism. Its two initial halt-spelling mistakes are preserved under `history/`; the final parser uses the manuscripts' inherited target-only halt label 254. No delivered artifact was changed.

## Machine comparison

The exact baseline is maintained `candidate-combined243/zfc_combined243_old.tm`, SHA256 `4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300`. The primary 242A table and Detour table both have SHA256 `c8ef2f44d25fee6813164cc59ec05061799397da8cf7f0ea7baab63d32d76e02`.

Detour deletes 27, changes `15/0` from `0 R 21` to `0 L 32`, and redirects `18/0`, `47/0`, `65/0` from 27 to 15. Its old-machine invariant is left-zero at states 15, 18, 47, 65 and current-zero at 27. The complete incoming lists establish the invariant from state 95 for any head and any binary function tape. The state map sends old 27 to new 15. Each old step is represented by one new step except old `15/0`, whose zero-preserving path through 32 and 45 takes three. Positive clocks and no intermediate halt yield both directions, as explicitly explained in `report.tex:125–224`.

Zero-branch deletes 15 and changes only `11/0` to `0 R 27` and `27/1` to `1 R 22`; its inherited table SHA256 is `6b700aa713418cfe347a6ff2d0a92de7c31810d1cf69814b4684c7fb463876a0`. Its weaker old invariant needs left-zero only at 18, 47, 65 and current-zero at 27. Checkpoints exclude old 15. At `11/0`, two old transitions match two or four new transitions according to the next cell; other feasible rows agree. See `paper/zero_reuse242_proof.tex:4–98`. This is a valid alternative proof presentation of the isomorphic machine, not a second independent fold.

The existing 17/39 fold remains the next deletion. Its changed rows do not touch the retained 15/27 renaming, and the two versions produce the same 241-state machine up to that renaming. This conclusion compares exact inherited labels and actions, not merely similar state counts. The ordinary proofs quantify over arbitrary function tapes; any existing Core/ListInt formalization has its separately stated finite-support scope.

## Detour: useful 1,768-bit construction

The recommended artifact is `research/equational1768/output/alias.json` and its matching bitstring, not `combined.json`. Its complete encoding has 22 equations, 420 term nodes, 11 symbols, five local variable codes and four-bit opcodes. The independent parser reconstructs exactly 1,768 bits, including the 49-bit header and both endpoints.

Three mechanisms are substantive:

1. Define membership by incidence after two updates: with `o = I(d,d)`, `B(x,y) = C(C(d,d,x),o,y)`, use `E*(x,y) = Inc(B(x,y),A(d,o))`. Empty-class and implication clauses separate d from o; update equations recover x and y. The explicit equality-predicate completion retains the function/Inc congruences needed for quotient interpretation, and the removed membership congruence follows from them.
2. Identify the auxiliary Boolean top with the existing source constant d. The ordinary upper construction uses an injection/retraction into a powerset Boolean algebra for an equality-free universal clause theory, with d mapped to top. The reverse uses an ultrafilter on predicate values while retaining the full carrier and source functions. It does not quotient arbitrary source functions by Boolean congruence.
3. Spend a symbol on the ground alias o while splitting ternary C congruence into two blocks. This reduces maximum variables from six to five, keeping symbol-plus-variable capacity at 16 and preserving four-bit opcodes. Reflexivity and the retained Euclidean equality law prove the partition equivalent to full congruence.

The ordinary consistency/rewrite equivalence depends on the inherited equality-complete FC13B calibration from Source 70. The delivered finite checks are transcription/certificate controls, not a new kernel theorem or internal PA calibration. The report correctly keeps its binary machine reduction independent of this packet.

## Combining detour with selector dispatch

Drop's contextual-reuse theorem can follow membership elimination, provided selector coordinates stay outside the equality quotient. For fixed actual selectors tV and tA, the recovered operations are `[H(tV,s,j)]` and `[H(tA,j,k)]`. Only the object coordinates require equality congruence. Never add an unstated requirement that equivalent selector values choose equivalent operations.

Membership remains definable by `Inc(C(C(d,d,x),o,y),H(tA,d,o))`. Its congruence proof uses C congruence, reflexivity of that identical ground H atom, and Inc congruence; it never changes the selector. The quotient's V and A operations are well-defined by the fixed-selector object congruences.

The naive combination crosses from 16 to 17 opcodes and loses the four-bit advantage. Two concrete variants are therefore being prepared separately by Drop: omit o and use the two-part C congruence (11 symbols + five variables); or retain o and split C and H's object coordinates individually (12 symbols + four variables). Exact NAND grouping and full serialization must be measured rather than subtracting the two reports' individual savings.

The independent `horn_certificates.py` in `/tmp/zfc-joint-equational-proof-review` provides 12 finite syntactic certificates with 49 inferences for both C partitions, fixed-selector H splitting, and the two membership-congruence forms. This supports the congruence step only; it does not silently discharge the model transformation or Boolean encoding obligations.

## Zero-branch: a genuinely different 1,169-bit frontend

The central new mechanism is the pair of unconditional native equations

```
V(P(x,s),d) = x
V(P(x,s),A(j,d)) = V(s,j)
```

The same A constructor serves as selector successor and atomic class constructor. Finite repeated tail/head equations give all needed selectors. Prepending supports de Bruijn binding directly. The descriptor reserves coordinate 2 for its class code, with y at 0, x at 1 and parameters starting at 3; the code is built before its containing descriptor, avoiding a recursive-code assumption. This removes conditional indexed-update equality and its explicit congruence completion. See `paper/stack_kernel_full.tex:46–93`.

The all-object upper model is concrete, not just a test on generated selectors: disjoint increasing codes for P/A/J/Q, externally terminating selector decoding, and structural class-code evaluation over a countable set-theoretic model. Each fixed descriptor relation is a finite pure-membership formula with finitely many parameters, even though the whole external decoder need not be internally definable. The raw EPSC empty-seed calibration remains an explicit dependency on Sources 14/08/40. This is ordinary ZFC metatheory, not a theorem covering arbitrary nonstandard internal formula codes.

Its Boolean conversion correctly keeps the two native equations on the same countably infinite carrier, equips that carrier independently with a Boolean algebra, and Booleanizes predicates. A general powerset/retraction extension would not preserve native equations. In reverse, the ultrafilter is applied only to predicates; native operations remain on the original carrier (`paper/stack_kernel_full.tex:156–178`). This distinction is essential when reusing the detour construction.

The explicit-Pick packet is exactly 14 equations, 214 nodes, 16 symbols, three local variable codes, five-bit opcodes and 1,169 complete bits. The proposed derived-Pick variant has fewer symbols but larger terms and is exactly 1,201 bits, so the explicit version is preferable under this format. The fresh own codec reconstruction matches both delivered bitstrings byte-for-byte including final newline.

Two narrowly justified combination observations:

- Truth fusion can preserve native equations by choosing the transported same-carrier Boolean algebra's top to be the already fixed d. This needs no powerset/retraction argument. The direct term replacement measures 1,166 bits, a three-bit header saving; opcode width remains five.
- Membership has the native-stack definition `E(x,y) = eps(P(x,P(y,d)), A(d,A(d,d)))`. Directly substituting it increases term size enough to produce 1,486 bits, or 1,483 with truth fusion. Thus the simple detour elimination is counterproductive here. These are exact syntax-only counts of the specified replacements, not new executed frontend certificates.

A separate same-carrier dispatch construction might pack stack operations using distinct actual selectors, but it would require a distinct native-equational model argument and complete term/arity accounting. The present equality-predicate selector-dispatch certificate must not be imported as though it already established that result.

The main outstanding implementation cost is a full binary ground-rewrite checker/enumerator with substitution, arbitrary one-hole contexts, both equation directions, fair certificate enumeration and blank initialization. Neither 1,768 nor 1,169 bits currently implies a smaller state count. The stack packet is the strongest distinct new encoding idea in these two reports; the detour transformations remain useful composable reductions on the existing Source 70 route.

## Review disposition

Retain both archives for their different encoding techniques. Reuse the existing 242A/241 machine lineage rather than treating their primary tables as additional reductions. No blocking mathematical discrepancy was found in the read ordinary constructions within their stated inherited-calibration scope. The static result and complete file pins are in `static-review.json`; newly authored reviewer failures and their corrections are preserved under `history/`.
