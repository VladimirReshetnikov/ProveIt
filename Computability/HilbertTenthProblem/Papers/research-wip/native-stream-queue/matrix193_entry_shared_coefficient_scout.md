# Share state pairs and matrix entries in the complete coefficient circuit

The complete source now costs **1,624 = 791M + 833A operations**, with the same **146 positive witnesses**, twenty outer residuals and exact degree **35,587** as its 1,679-operation parent. The saving is **55 operations: 10 multiplications and 45 additions/subtractions**. It changes only the four fixed coefficient-polynomial producers. The entire final polynomial is identical on every supplied tuple over every commutative ring.

This remains an alternate ordinary-input matrix route above the established 84-operation universal bound. The controller, 340 selected-coordinate lanes, eight fixed program coefficients, bounded-high chart, native kernel, ordinary-input bridge and fixed recipe are unchanged. This packet does not include the separate controller-flow rewrite and makes no circuit-minimality claim.

## 1. Exact source and provenance

The immediate parent is [the complete composed source](matrix193_composed_output_scout.md). The new [helper](matrix193_entry_shared_coefficient_scout.py) and [receipt](matrix193_entry_shared_coefficient_scout.json) save all 1,624 live rows, the complete supplied-port list, the four dense coefficient certificates and the whole-output identity. The helper adapts the earlier structured compiler and cut-audit routines by source copying, then adds the state-pair, trace and integer-affine transformations below. No predecessor Python is imported or executed.

| Inert dependency | SHA-256 |
|---|---|
| Composed Python | `e8b2982bdf00a9be6e6e80a1b86c38f3536a5345c60adf3103e8f7356ed01317` |
| Composed JSON | `a231b3ef66f0ab0f729bf50e40f87fad5a5d784e089249dbb4e93e11696a9e37` |
| Composed proof | `83711eab17b18f38c2bd47ddd3d803fde5adf339f7b5bbc0be2839a3bfeff748` |
| Structured Python | `39ab5c942af5bd6d725d2c17e89d2222e3e44bf26cc59e3c1bad1d4e011e10a9` |
| Structured proof | `8e49bed183eed196768951d3a86febc6cbd8d0a2e8898387c41b3b0e0ebeced3` |
| Gamma1 matrix JSON | `9cdd0274625c847aa77f5907ba6554ee16f37895f5c026b3d776595330676668` |
| Gamma1 matrix proof | `6349644283548af96f4a9582ee32d959a123c81bf1c2f902c45874ae45c96742` |

The helper authenticates all seven files and the composed receipt's source hash. It reconstructs the actual copy, rewrite, cleanup and LOAD matrix words from the saved twenty-letter matrix map. The former [structured word factorization](matrix193_structured_coefficient_scout.md) remains the starting identity, including the noncommuting left-boundary term. The numerical matrices are fixed program-independent data; all their uses in the evaluated circuit are paid.

## 2. Pair the two scanned symbols before evaluation

Use t=Q² and z=Q⁶. Write T0=Psi(0), T1=Psi(1), L=Psi([), R=Psi(]), and

    C_R(t)=T0*t²+T1*t+R,
    C_L(t)=T0*t²+T1*t+L,
    V(z)=z*T0+T1.

The parent's 29 source-state triples are indexed in their original order. Every state except J contributes adjacent scan-0 and scan-1 triples; J contributes only scan 0. Group the fixed state matrices, retaining their exact original powers, as

    B_RR = Psi(A)*z^27 + Psi(B)*z^25
           + Psi(K)*z^8 + Psi(L)*z^6 + Psi(O),
    B_LL = Psi(C)*z^23 + Psi(D)*z^21 + Psi(F)*z^17
           + Psi(G)*z^15 + Psi(H)*z^13,
    B_RL = Psi(E)*z^19 + Psi(I)*z^11,
    B_LR = Psi(M)*z^4 + Psi(N)*z^2.

The two letters in each subscript specify the transition directions on scanned bits 0 and 1. Thus there are five RR states, five LL states, two RL states, two LR states and the single J0 transition. These are checked against the literal source words, not inferred from state names.

The two matrix polynomials multiplying the right and left triple patterns satisfy

    A_R = B_RR*V + z*B_RL*T0 + B_LR*T1,
    A_L = B_LL*V + B_RL*T1 + z*B_LR*T0
          + z^10*Psi(J)*T0.                              (1)

For example a pair of right-moving words with the same state contributes Psi(q)*(z*T0+T1) times the lower of its two z powers. A mixed pair contributes one term to each of A_R and A_L. Expanding (1) reproduces all 29 original word-matrix coefficients in place. No matrix factors are commuted.

The Y triple section is still A_R*C_R+C_L*A_L. The emitter evaluates its row (Q,1) by sharing the row (Q,1)*C_L and the four state sums. The copy prefix, cleanup suffix, LOAD matrix, scalar identity subtraction and all X triple formulas retain their exact values. This is a fixed integer matrix-polynomial identity; it uses no trajectory or zero-set assumption.

## 3. Share trace-two entries and support polynomials

Four matrix sums in the emitted schedule have only zero coefficient matrices or fixed state-letter matrices of trace two: the two X left-moving sums and B_RR, B_LL above. For such a sum M(z), let S(z) be its support polynomial, with one coefficient at every occupied state position. Write a(z), b(z) for its top-left and top-right entries. For a fixed common lower-left value w, put

    correction(z)=sum_j (M_j[1,0]−w)*z^j

on occupied positions, and zero elsewhere. Then, entry by entry,

    M(z) = [[a(z), b(z)],
            [w*S(z)+correction(z), 2*S(z)−a(z)]].       (2)

The helper checks the trace condition on every occupied fixed coefficient, chooses the most frequent lower-left value, and independently verifies all four entries of (2). The common values are −20, 5, −20, 5 respectively. All scalar multiplications and subtractions in (2) are paid.

The four actual supports have short exact products:

| Matrix sum | S(z) |
|---|---|
| X left, written 0 | z²(1+z)(1+z^14)+z^13(1+z^5) |
| X left, written 1 | z^8(1+z)(1+z³+z⁶) |
| Y RR | (z⁶+z^25)(1+z²)+1 |
| Y LL | z^13*((1+z²)*(z^8+z²)+1) |

Their support sets are, in the same order,

    {2,3,13,16,17,18}, {8,9,11,12,14,15},
    {0,6,8,25,27},    {13,15,17,21,23}.

The helper expands each displayed product and checks the entire coefficient list before using it. Every power is computed by paid multiplication or reused from a proven equal paid register. The support identities introduce no variable division, bit lookup or uncharged polynomial evaluation.

The compiler also permits an integer-affine reuse P(Q)=s*T(Q)+c when an earlier register T has that exact relationship in every coefficient, with integer fixed numerals s,c. It pays the required multiplication and addition, or a single addition/subtraction when s=1 or −1. Nonintegral ratios are rejected. Normalizing coefficient vectors is a compile-time method for finding identities; it is not a runtime operation or a supplied oracle. Full independent coefficient expansion checks the emitted expressions after all such choices.

## 4. Complete paid source and all-value proof

The emitter first produces 582 candidate component rows. Four unused rows are removed by output liveness, leaving **578 = 329M + 249A** live component rows. These replace the parent's **633 = 339M + 294A** rows. The complete source preserves the other **1,046 parent rows**, apart from references to the four equal polynomial cuts:

| Old coefficient output | New output | Degree in Q |
|---|---|---:|
| `mix323` | `cp312` | 143 |
| `mix324` | `cp313` | 143 |
| `mix631` | `cp580` | 193 |
| `mix632` | `cp581` | 193 |

A second sparse interpreter expands every new pure-Q register and verifies all four complete coefficient lists against the parent. The source audit checks that no deleted private register escapes except through those four cuts. It then replaces each proved equal pair by a common formal atom and interns every surrounding operation. All 1,046 retained registers and the complete final output agree exactly.

Consequently

    F_1624 = F_1679                                    (3)

as integer polynomials, hence over every commutative ring. All supplied coordinates, including every bounded high hat, low/dot hat or slack, selected block, native witness, edge/state coordinate and ordinary input, are retained literally. Thus the positive zero set is identical, without a new witness map. On the unchanged valid fixed-program slice, the inherited ordinary-input theorem and full positive native completeness transfer directly. Arbitrary fixed-port values are not asserted to be programs.

| Complete source | M | A | Total | Positive witnesses | Exact degree |
|---|---:|---:|---:|---:|---:|
| Composed parent | 801 | 878 | 1,679 | 146 | 35,587 |
| Entry-shared successor | 791 | 833 | 1,624 | 146 | 35,587 |
| Saving | 10 | 45 | 55 | 0 | 0 |

All new rows and supplied ports are live. The array has 137 distinct integer literals, separate from its unchanged eight fixed coefficient ports. Its fixed numeral recipe uses exact integer matrix words, sums and products. No use of a fixed coefficient in the runtime arithmetic is omitted from the count.

The exact degree follows from (3), including on every valid fixed-program specialization. In particular the parent's bounded-high degree tie remains: the leading extraction bracket contains a nonzero SWITCH-edge coefficient C*K/2 absent from the final block selector. The component rewrite changes none of that polynomial. The exact total remains native degree 34,039 plus SOS degree 1,548. No new dense expansion of the degree-35,587 full polynomial is claimed.

## 5. Fresh checks and limits

The receipt saves the full source, source SHA-256, seven dependency pins, all read-pair and trace-two records, coefficient certificates, complete cut identity, operation ledger and liveness proof. Thirty-two fresh signed full-source evaluations over two prime fields compare every retained register, every changed cut and the final output; half use the saved actual fixed binding and half vary all fixed ports. These are supplementary arithmetic checks, not native accepting histories.

The unchanged 303-gate, 51-witness diagnostic is identified by its source-array hash and inherited ledger. It lacks the actual state-pair structure; no new diagnostic source or saving is claimed. The parent's large accepting outer fixture is not rerun, and no new giant trajectory or native Pell witness is materialized. Polynomial identity supplies the semantic transfer.

After installation, run from any working directory:

```sh
entry_wip=/absolute/path/to/native-stream-queue
python3 "$entry_wip/matrix193_entry_shared_coefficient_scout.py" \
  --root "$entry_wip" --expect "$entry_wip/matrix193_entry_shared_coefficient_scout.json"
python3 -O "$entry_wip/matrix193_entry_shared_coefficient_scout.py" \
  --root "$entry_wip" --expect "$entry_wip/matrix193_entry_shared_coefficient_scout.json"
```

Generation uses `--write` instead of `--expect`. JSON parsing rejects duplicate keys; receipt comparison is recursive and type-exact. Explicit checks remain active under optimized Python.

Fresh generation and fresh normal and `-O` exact receipt replays from `/` pass on the frozen source and receipt. All recorded tuples are serialized as JSON-native lists; no predecessor script was executed.
