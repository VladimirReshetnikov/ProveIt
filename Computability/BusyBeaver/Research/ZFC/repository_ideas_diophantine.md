# Diophantine and list-coding ideas for the ZFC machine

Source inspection and a new isolated encoding experiment, 16 October 2026.

The most useful transfer is to make the stored code match the verifier's elementary operations. The native-stream queue work removes an unnecessary layer of queue-content history by using streams at their own radix. For our formulas, a direct stream of small token fields can likewise avoid repeatedly packing an ever larger tail through a quadratic pairing function. A new 2-adic list experiment gives a concrete, reproducible example: the same two concrete NAND3 formulas cost **2831 framed bits instead of 3080**, with all variable and binder fields charged. This is an encoding comparison, not a machine-state improvement. The greater potential benefit is a pair/unpair routine using shifts and a count of trailing zero bits rather than Cantor inversion.

## Inspected repository interfaces

These are source-level findings, not fresh builds of the Diophantine or ListCoding projects. The current machine target remains a ZFC proof relating the literal binary machine's nonhalting to Con(ZFC). None of the declarations below alone proves that endpoint.

| Source and exact location | What it supplies | Transfer to this project |
|---|---|---|
| `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1978/Pairing.lean:25` (`J`), `:29` (`two_J`), `:54` (`J_injective`), `:72` (`KL`), `:92` (`J_K_L`), `:109` (`K_J`), `:113` (`L_J`) | Cantor pairing and inverse laws. The displayed inverse walks through successive diagonal positions recursively. | A strong correctness reference and a fair arithmetic baseline. Do not assume that this proof-oriented inverse is already a small executable TM subroutine. |
| `Logic/PeanoArithmetic/ListCoding/Lean/PAListCoding/Basic.lean:20` (`encode`), `:37` (`encode_injective`), `:49` (`valid_iff_existsUnique_encode`), `:78` (`decode`), `:83` (`encode_decode`), `:87` (`decode_encode`) | Exact representation and guarded roundtrips for Ackermann-coded sequence graphs, specialized from Foundation. Both `encode` and `decode` are declared `noncomputable`. | Reuse the interface design: validity, both roundtrips, uniqueness and indexed lookup. It is not an executable codec to insert unchanged into the small machine. |
| `Logic/PeanoArithmetic/ListCoding/README.md:29`, `:33`, `:117` | Malformed-code and validity conventions; different numeric encodings are allowed when their representation contracts agree. | A totalized parser's default result must never certify a malformed formula or proof. Our natural-field lists are all valid as lists, but most are invalid as formulas. |
| `Logic/PeanoArithmetic/ListCoding/Lean/PAListCoding/ExactTrace.lean:20` (`ExactIter`), `:32` (`exactIter_iff_exists_sequence`), `:76` (`BetaTrace`), `:90` (`exactIter_iff_exists_betaTrace`) | A finite exact run has an equivalent sequence and a fixed two-natural beta-code interface; every adjacent step is still checked. | Separate history storage from transition validity. A fixed number of outer fields does not make verification of an arbitrarily long trace free. |
| `Logic/PeanoArithmetic/ListCoding/Lean/PAListCoding/BoundedDioph.lean:175` (`BetaModulus`), `:182` (`BetaEntry`), `:203` (`BetaEntry_functional`) | Modulus/remainder lookup and functionality. | A precise alternative for later arithmetic trace certificates; compare its modulo machinery against direct stream/list lookup in the actual backend. |
| `Logic/PeanoArithmetic/ListCoding/Lean/PAListCoding/BoundedCipherDioph.lean:203` (`boundedForall_dioph`) and `IterationDioph.lean:135` (`exactIter_dioph`) | Variable-bound elimination and exact-iteration closure, with explicit cipher/code/index/multiplication interface hypotheses. | A future path to a Diophantine search formulation. It does not provide an already-paid tiny formula/proof interpreter or an internal ZFC proof transformer. |
| `Logic/PeanoArithmetic/ListCoding/Lean/PAListCoding/SparseCipher.lean:43`, `:47`, `:50`, `:55`, `:358`, `:428`, `:702` | Sparse powers-of-two digit positions, bounded well-formed ciphers, injectivity, pointwise addition and a product-diagonal extraction theorem. | Store columns so the operations the verifier actually uses become simple identities, while retaining the no-carry bounds. The large sparse integers can make arithmetic representation simpler while making literal binary data larger. |
| `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1980/GraphRun100.lean:52` (`path_run`) | Recovers exactly one state per row and permitted graph edges from a packed routing relation and explicit support/bound/shift hypotheses. | Packed proof or computation rows must force a valid path; do not assume the proposed rows already select legitimate states or inferences. |
| `SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/Coding.lean:156` (`formCode`), `:202` (`formCode_tag_ne`), `:215` (`formCode_inj`) | Tagged set-theoretic quotation, tag disjointness and injectivity. Lines 52–55 explain why a variable slot needs no extra tag once its constructor fixes the payload role. | Let the token determine payload arity. Avoid another type marker for every binder/operand, but keep a strict constructor parser. These are internal set codes, not the natural/tape codec being optimized here. |
| `SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/CodedDerivation.lean:64`–`:101` | An explicit circular-justification failure of unranked derivation closure, followed by ranked certificates with strictly smaller premise ranks. | A sequential proof list can use earlier-line references as its rank. The validator must check strict descent; merely finding a finite set closed under inference is unsound. |

The ListCoding README explicitly separates standard-model evaluation metatheorems from internally derived PA theorems at `Logic/PeanoArithmetic/ListCoding/README.md:340`–`:345`. That distinction also matters for our ZFC target: the encoding theorem, proof-checker theorem and theorem about the final literal table are separate obligations.

## The native-stream lesson, including its limits

The concrete FIFO identity is in `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_NATIVE_STREAM_RAW_QUEUE.md:22`–`:49`. With a queue of length `m`, `W=3^m`, a history of length `t`, `q=3^t`, and the stated bounds,

```text
D + q*F = I + W*A.
```

The stream of removed symbols is `D`, the appended stream is `A`, and `F` is the final queue. The special equation `D=I+W*A` captures a zero final queue only with the stream bound `D<q`. The same note gives a counterexample to deleting that bound at lines 58–62.

The useful change is representational: lines 123–127 remove the wider time radix and two content histories by using base-three streams directly. The remaining power and synchronized-controller predicates are explicitly external at lines 129–133. Lines 64–95 require both coordinate streams to use the same path and the same positions. This suggests keeping formula tokens, operand fields, and proof-rule hints in one synchronized certificate format, rather than maintaining independently guessed views that a checker must reconcile afterward.

There is no inference from that note's six/eight arithmetic operations to six/eight TM states. Its subtotal excludes the controller and power predicates. Likewise, the five-signal results are about five **live signals**, not five-state binary Turing machines. The bounded review at `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_new_signals_0d7f51c44.md:20`, `:24`, and `:36` retains program-dependent rule tables, 19/39 speeds, 32/54 contacts, and a horizon-dependent number of arithmetic witnesses. Those are interface ideas, not a competing Busy Beaver bound.

## A new direct streaming tuple code

The following code is a new experiment in this research directory, not a claim that the inspected projects already formalized this exact encoding.

```text
Nil        = 0
Cons(a,b)  = 2^a * (2*b + 1)
Uncons(c)  = (v2(c), c >> (v2(c)+1))       when c > 0.
```

Zero is reserved for the empty field list. If `c>0`, its odd part is uniquely `2*b+1`, so `Uncons` recovers the unique head and tail. Moreover

```text
b < 2*b+1 <= Cons(a,b),
bit_length(Cons(a,b)) = a + 1 + bit_length(b).
```

Thus each nonempty-list decoding step strictly decreases the current natural, and a list of fields `a₀,...,aₙ₋₁` has **exactly** `Σ(aᵢ+1)` bits. Induction on lists proves decode-after-encode. Strong induction on the natural code, using the strict tail decrease, proves encode-after-decode. This is a complete elementary mathematical codec argument; no Lean arithmetic proof of these 2-adic identities is claimed here. The existing ListCoding roundtrip declarations establish the desired contract for a different representation and cannot simply be cited as proofs of these identities.

In least-significant-bit order, one field is `0^a 1`, followed immediately by the tail. For a formula, flatten each postfix token as its constructor tag followed by the payload fields determined by that tag:

```text
mem:  tag 0, then two variable labels
NAND: tag 1, no payload
all:  tag 2, then one binder label
eq:   tag 3, then two variable labels, only in equality mode.
```

The natural list code can be decoded by shifts and counting factors of two. It does not need a quadratic operation on the large tail, a square root, or a search through Cantor diagonals. On the other hand, a field of value `a` occupies `a+1` bits, so it is attractive for the small labels after alpha reuse and may be poor for large variable indices. Gamma-coded fields remain a control.

For comparison, a right-nested Cantor list uses `1+J(a,b)`. Once the tail `b` dominates the small head, this is quadratic in `b`; repeatedly nesting tails therefore approximately doubles the bit length per field. Binary-interleaving pair functions avoid square roots but can still approximately double the large tail's bit length when nested in this unbalanced list shape. A balanced pairing tree has a different size/decode tradeoff and must pay for its shape. These are mathematical observations about alternatives, not new measured decoder state counts or claims about every use of pairing.

### Fair framing and executed comparison

A natural-register code has an assumed zero-test and existing natural-number boundary. Its low-to-high binary numeral is **not** a self-delimiting stream: a list's bits can be a prefix of a longer list's bits. The binary comparison therefore retains the earlier experiment's full outer frame:

```text
mode bit || gamma(payload_bit_length + 1) || payload.
```

Both decoders reject trailing bits, truncated fields, malformed RPN, forbidden equality and noncanonical equality mode. The new decoder additionally rejects a noncanonical natural numeral. A theory-list container and decoder program remain uncharged in both formats.

The input is exactly the existing experiment's double-negation-normalized, alpha-reused NAND3 encoding of the two concrete formulas: one-way profile congruence and the subset-only subset-seeded wrapper instantiated with `Mem(0,1)`. This single matrix instance is not the infinite schema.

| Concrete formula | Natural fields | Natural-register payload bits | Full new frame bits | Earlier gamma frame bits |
|---|---:|---:|---:|---:|
| One-way profile congruence | 153 | 293 | 311 | 323 |
| Subset-only subset-seeded wrapper, matrix `Mem(0,1)` | 1353 | 2496 | 2520 | 2757 |
| Separate-formula total | 1506 | **2789** | **2831** | **3080** |

The fair framed saving is **249 bits**, about **8.08%**. The unframed total of 2789 is reported only at the natural-register input boundary. All six assignments of tags 0,1,2 were tried; `mem=0`, `NAND=1`, `all=2` minimizes these payloads among those six assignments. No global coding optimality follows.

The tests cover 3906 lists of length at most five with entries below five, all natural codes below 65536, strict tail descent and exact bit lengths, 100 larger random head/tail cases, concrete formula/frame roundtrips and strict malformed-input rejection. The earlier eight `kernel_metrics` tests also pass after tightening equality-mode canonicality. Reproduce with:

```sh
uv run --no-project python Computability/BusyBeaver/Research/ZFC/test_stream_encoding.py
uv run --no-project python Computability/BusyBeaver/Research/ZFC/stream_encoding.py
```

Implementation: `stream_encoding.py`; tests: `test_stream_encoding.py`; deterministic output: `results/stream_encoding.json`. `kernel_metrics.py` and its tests retain the original gamma-framed comparison. No delivered code was edited, no external suites were rerun, and no Lean build was used for this experiment.

### Why the decoder may matter more than these bit counts

Every supported concrete formula has a finite positive natural code. Fair enumeration of natural candidates therefore reaches it. That fact does not authorize accepting arbitrary decoded fields: the parser must still enforce constructor arities and stack shape, and the proof checker must enforce logical rules, freshness, schema instances and strictly earlier references. Changing this storage codec must preserve those gates.

The likely implementation experiment is to replace the arithmetic pair/unpair routines in a single existing backend and compare complete literal tables. Counting shifts and multiplying/dividing by two could reduce control code even when runtime becomes enormous. Conversely, a compact data stream can lose if its decoder, canonical-boundary handling or traversal routines need more states. Both outcomes remain possible.

The selected NAND3 representation also expands negation/implication trees: these two concrete formulas contain 752 NAND-basis nodes, compared with 56 nodes in their normalized negation/implication basis. A smaller constructor alphabet can enlarge literal axiom data. Keep the four-constructor membership/negation/implication/forall route beside NAND3, and distinguish a compact axiom-generator program from an expanded literal tree. The current experiment does not compare those full generators.

## Concrete next steps

1. **A/B the actual pair/unpair backend.** Preserve the same calculus, axioms, proof target, fair enumeration and tape conventions. Swap only the structural Cantor codec for this direct natural-field stream. Count complete emitted states, including natural zero/boundary tests. The mathematically verified tail decrease is the termination invariant for decoding.
2. **Keep proof references acyclic by construction.** Sequential line numbers or checked backward distances can supply the rank used in `CodedDerivation`; test cyclic and forward-reference certificates explicitly. This applies the existing soundness lesson without importing its much larger internal set-code representation into the runtime machine.
3. **Use native token and witness streams.** Let constructor tags determine the next payload arity, and keep all views of a proof step synchronized. A source formula/matrix and its fresh-variable certificate must refer to the same code. This is the operational analogue of the native queue's common-history requirement.
4. **Use beta/sparse-cipher packing only after measuring the checker.** The existing declarations offer a rigorous path for arithmetic trace compression, but their modulo, power, column-validity and no-carry machinery has not been paid in this backend. Sparse witness packing is attractive when it simplifies the fixed checker more than it costs to decode; a smaller Diophantine variable count alone does not establish that.
5. **Keep mathematical and machine endpoints separate.** A Diophantine compiler's number of variables, degree, arithmetic gates, signal count or word length is not a binary TM state count. Any successful representation change still needs the ZFC theorem about the final literal table and the chosen Con(ZFC) proof predicate.
