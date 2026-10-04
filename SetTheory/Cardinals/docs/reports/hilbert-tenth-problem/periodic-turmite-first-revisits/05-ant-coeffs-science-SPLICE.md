# Explicit literal prefix-to-main splice

Status: both complete joined sources have now actually been generated in a streaming pass, topologically/domain checked and hashed. `verification/joined-strict-receipt.json` records the results. The prefix is 29,081,374 gates; the joined two-input source is 31,388,831 gates and the joined one-input source is 31,388,841 gates. The arithmetic records are generated and hashed without materializing giant integer values or retaining the entire source file. This computation reuses only the inspected, authenticated own-code Report44 arithmetic generator and its three reconstructed component specifications, not upstream physical-ant code, color recipes, or upstream saved schedules.

## Objects and binding map

Let P be the exact source emitted by `full_prefix.build`, let N=29,081,374, and let L be the returned `labels` dictionary. P starts with literal leaves `one`=1 and `three`=3, and its gate IDs are 0,...,N-1. An integer operand in P is a reference to an earlier gate; it is never a free integer literal. Every value of L is either one of those two literal leaves or a gate ID less than N.

L contains precisely the following 1,152,598 distinct keys:

- tile:0,...,tile:575999
- first:0,...,first:575999
- anchor:0,...,anchor:583
- Cu,Cx,Cbase,C198,EndpointK,EndpointD
- 0,1,2,3,4,6,8,9

The two authenticated main-source receipts certify exactly the same coefficient-port set by their counts, categories, and ordinary-numeral inventories. In particular no C:-1 occurs in either main source, even though the older generic validator would also recognize that spelling. The signed anchor builder uses a paid internal minusOne wire; that wire need not be a main coefficient port.

Define phi(C:k)=L[k]. This is a total fixed binding for every old coefficient operand. It is not a new input declaration, witness, free parameter or arithmetic operation. `phi(C:0)` is the paid prefix gate 0. `phi(C:1)` and `phi(C:3)` are literal leaves. Every other phi value is a paid prefix gate.

## Mechanical transform of every main record

Let S_a be the authenticated canonical old main source for arity a. Its identities are:

- a=2: SHA256 c16901162e09b07d1e0c27b28e29dcc12a9b6137391fce85e3f150a3fed37eac, 2,307,457 arithmetic gates
- a=1: SHA256 85a161972769207e4f5d4212214630535208f69d6736bca2b46a8aff8276a22a, 2,307,467 arithmetic gates

For each old operand t define sigma(t) by these disjoint cases:

1. An old integer gate reference r is changed to N+r
2. An old fixed-coefficient string C:k is changed to phi(C:k)
3. A declared raw or positive-witness coordinate name is preserved literally
4. Any other operand is rejected

The joined source is P followed by this record-by-record transform of S_a:

- `[r,op,a,b]` becomes `[N+r,op,sigma(a),sigma(b)]`, with the same opcode
- `['raw_positive',names]` is preserved
- `['positive',name]` is preserved
- `['residual_pair',j,a,b,section]` becomes `['residual_pair',j,sigma(a),sigma(b),section]`; this remains metadata, not a new equation
- `['eq',a,b]` becomes `['eq',sigma(a),sigma(b)]`

There are no coefficient declarations in the joined source and no C: operand survives. Every old multiplication and addition/subtraction is retained, including operations with a zero- or one-valued fixed factor. Aliases do not delete or discount any old operation.

The raw/positive declarations may appear after the input-independent prefix. They remain before every main use in their original order. For a=2 the raw names are RawLeft,RawRight and the same 465 coordinate names remain existentially positive. For a=1 RawInput is raw, while RawLeft and RawRight remain the first two of the same 467 positive-witness names. No prefix wire is a new witness.

The old final equations map exactly to:

- a=2: gate 31,388,830 = gate 0
- a=1: gate 31,388,840 = gate 0

The right side is therefore a paid expression for zero, not an unpaid zero literal. The old 285 or 286 residual pairs remain only metadata, and the only final asserted equation remains the sum-of-squares equation.

## Topology and equivalence proof

All prefix gates are topological by the checked new source. An old main gate r could only reference an earlier main gate q<r, a fixed coefficient, or a previously declared coordinate. After transformation, N+q<N+r; every prefix reference is <N; and declarations are unchanged. Thus the entire formally spliced source is topological, with leaves only literal 1, literal 3 and the declared coordinates.

The coefficient construction proves L[k] equals the old prescribed value of C:k for every key. Since P has no variable dependencies, induction on old gate r proves its translated gate N+r has exactly the same integer-polynomial value for every assignment of the raw/witness coordinates. This includes all residual operands and the final zero operand. Hence the joined single polynomial is pointwise identical to the old one, not merely equisatisfiable after hidden substitutions or added input bindings.

Therefore the inherited positive domains, 465/467 witness counts, one asserted equation, and exact degree 2,304,000 are preserved. Counts add without a further arithmetic binding cost:

- a=2: 13,182,377+1,153,586=14,335,963 M; 15,898,997+1,153,871=17,052,868 A; total 31,388,831
- a=1: 13,182,377+1,153,590=14,335,967 M; 15,898,997+1,153,877=17,052,874 A; total 31,388,841

`check_splice_contract.py` performs a limited static inventory/count/domain check from the receipts. Its receipt remains explicitly labeled static. In addition, `join_strict.py` now performs the actual full binding and streaming check just described. It reproduces both old-main canonical hashes, actually observes all 1,152,598 fixed-coefficient labels in each main stream, binds every occurrence, verifies all declaration/reference constraints, and validates the sole final paid-zero equation. No C: operand or free coefficient declaration survives.

The complete joined stream hashes are:

- a=2: b235ba1d2baf0cf089c9658b1995f9c19fbe3ff033dc6ae67c76ec8cd6522d03
- a=1: 737866317089c07465253a0d489813bf1bab50aaba0dda6083acbf78ef45f276

Canonical arithmetic records are TSV `id opcode operand operand` lines; transformed raw/domain/residual/final records are compact JSONL in the old source order. This differs deliberately from the older all-JSON record encoding, so the new hashes should not be compared with the old hashes as byte identities. The adapter separately verifies the unchanged old-main hashes before accepting each result.
