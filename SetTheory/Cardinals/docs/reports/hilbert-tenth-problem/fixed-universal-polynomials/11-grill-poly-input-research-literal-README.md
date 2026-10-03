# Literal fixed U15 / tag / Genera source packet

The deterministic source is `build_literal.py`. It executes only this packet's own code and the Python standard library. The full output `literal_tables.json` includes all U15 tokens, the numeric refined-state table, every tag production, every normalized Genera production, a total ignored halt row, initial-format metadata, and unique-halt metadata. It contains no arithmetic/history circuit.

## Exact emitted table counts

- U15: 15 states, 29 instructions, two tape symbols; sole missing instruction (u10,b)
- Refined read states: 30, with start0=(u1,c), halt19=(u10,b), 29 nonhalt instructions (15 left,14 right)
- Tag: 570 symbols and 570 total rules; output lengths1/2/3/4 occur59/436/29/46 times
- Genera: 1,013 symbols, including569 original nonhalt symbols, one dummy,442 distinct pair symbols and one halt
- Genera nonhalt phase rows:2,024; all exactly two outputs. With the ignored total halt row:2,026 phase rows
- Width-one symbols:569; width-zero symbols:444, including the semantically irrelevant halt width
- The corrected Grill schema would use397,488 phases and E width198,744 for each original input symbol. It has not been emitted here

All unspecified original fillers are explicitly inert. Fresh HALT is emitted only by the accepting A:19 rule before normalization; after normalization only its unique pair emits HALT. Input words cannot initially contain HALT. The full raw-binary input restriction of the older exact-width loader is not silently enlarged: this table's accepted interface is the framed unary source word supplied by the new semantic contract.

## Semantic proof and source pins

The complete proof is the preserved `../SEMANTIC_CONTRACT.md`, pinned in `source_manifest.json`. It gives the right and left macro cuts, the explicit prime rotation for left moves, no-short-queue proof, unique accepting head, normalization phase proof, input orientation and arithmetic loader interface. This packet specializes that finite recipe to each literal U15 row.

The original U15 PDF and Table16 page image are included and hashed. The frozen upstream Python is stored as `.py.txt` and is data only; it was not executed. The Cocke–Minsky PDF and both rule-page images are preserved in the parent directory and hashed. This construction explicitly corrects the local t0 production to include its final filler; the primary print discrepancy and ten-step counterexample are documented, without claiming an author-published erratum.

The constant `H` in the tag table is not short-word halting. Valid simulations emit this fresh symbol only on entering the designated accepting control. The normalized Genera unique-H and hypothetical-prefix conditions hold on the complete valid canonical-input slice, including rejecting runs. The corrected Grill bridge's phase and exact first-empty cleanup results can therefore be applied without alteration.

## Two distinct recoder interfaces for later composition

Name the first interface `canonical_input_bits`: input u=x+1, canonical bit-length guard, width32, output the LSB block spread. It binds the positive right tape integer N by the signed-coefficient frame equation.

Name the second interface `unrestricted_tape_exponent`: full recoder specialized to input1 and spread output1, fixed width397,488, with exact-duration extraction and ell=N+1. It must have **neither** the canonical-length guard **nor** the dyadic-duration predicate. Its positive exponent is h=N+1>=2. The proof explicitly bounds h<B-1 to eliminate modular aliases.

The program coordinates (a_e,p_e,s_e,C_e,L_e) are fixed positive parameters for a represented set, not existential witnesses that may select a program depending on x. The table is fixed. The external x is positive and unchanged except for its explicitly paid x+1 shift. All remaining coordinates used by the two recoders, tape binding, exact unary loader and native history are existential positive witnesses.

Every eventual comparison must enter the same finalizer:

    U * (1 + sum of all nonunit residual squares) - 1.

The native history unit U is retained; the two full recoders, canonical guard, tape-value binding, exponent extraction, unary-value relation and exact width relation are all inside the sum. Adding a loader sum outside a potentially negative native polynomial is invalid.

## Reproduce bounded tests

    python3 build_literal.py --expect
    python3 check_literal.py
    python3 resource_estimate.py

The own literal checker tested every actual nonhalt state over M,N=0..9:2,900 macros, plus348 multistep seeds and2,746 consecutive actual transitions. Across these it executed813,202 tag steps, exercised all29 nonhalt states, and found minimum preacceptance length3. It also checked400 arbitrary two-generation projections and96 full normalized unique-H traces using exact dummy-run compression, including their phase, first H position and exponentially growing physical lengths. These tests are finite evidence, not a proof of universality or a full positive Pell tuple.

The separate `review_*` files contain the independent literal audit. That audit checks the primary U15 image, all actual productions and normalization rows, and independently updates sparse tapes rather than using the builder's transition helper.
