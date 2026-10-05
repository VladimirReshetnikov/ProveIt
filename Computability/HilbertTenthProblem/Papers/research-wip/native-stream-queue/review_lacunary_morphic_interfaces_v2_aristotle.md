# Scope review: lacunary coefficients and morphic histogram compression (corrected version)

This corrected version supersedes the first frozen scope review; that MD/JSON pair remains unchanged and is bound in the receipt. Review remark 3 retains the reviewer's omitted degree qualification and its correction.

Two unplaced incoming reports merit bounded follow-up as arithmetic/compression leads. Neither is established here as a Turing-complete substrate, a fixed-arity ordinary-integer compiler, or a source of a paid operation saving. This is selected-interface reconnaissance, not a full theorem audit, source-code review or replay of the delivered evidence.

The reconnaissance inspected recent local origin/main history through b1cd01f280d57f22e6c83e1e60bb2148a4278c8e, the incoming index, and the WIP review census. It excluded the already scoped batch103 closed-lambda109/110 reports. No exact-name or selected-topic review for the two leads was found in that WIP search; this is a bounded search result, not a claim that nobody has reviewed them. Both archives remain byte-identical to their arrival in commit e4d5dcf9ec36364bd45b61d5a5bef4e1ef96e97b (5 October 2026).

## 1. Immutable provenance and actual reading

| Archive at the arrival commit | Git blob SHA1 | Whole archive SHA256 |
|---|---|---|
| docs/incoming/Digit_Sum_Divisibility_in_Lacunary_Iteration.zip | ceaaf7def0a65d93cdc94bc2a57ca98eb2c3b65a | 42c5dc7ac2f3c4d2ad0668406aad794ff9ab0678c46409111f3ad94d55eea6a1 |
| docs/incoming/binary_morphic_fluctuations.zip | 9379c4dd8b4e73e192cd475625f160a81f35d424 | 2154f5d52f9c2b6f1b708545f88aec600b294a0418b76524fabfed28c61fdc74 |

The first archive is 581357 bytes with 16 file members; the second is 1827453 bytes with 29 file members. The companion JSON inventories and hashes the whole uncompressed bytes of every member. Hashing a member is not a semantic read, test or certification of it.

The lacunary manuscript is `lacunary_digit_divisibility/article.tex`, 1565 lines, SHA256 `6f4df0bc78c8a913efc9070c1aec4b591589fc24116adfe866eb9bebdf81c03a`. Read: title/source header lines1–50 and substantive spans80–110,160–224,1028–1101,1175–1216,1325–1350. The full delivered `README.txt` was subsequently read. The morphic manuscript is `binary_morphic_fluctuations/binary_morphic_fluctuations.tex`, 2187 lines, SHA256 `3aca17e07871d8dc110d5112c610bf2a59910c7fa919e16ab38df31660df2f74`. Read:70–98,255–283,323–420,1037–1105,1288–1308,1898–1916,2028–2037, plus its full `README.txt`. Section/theorem/keyword navigation over the manuscripts located these spans; it was not a full prose read. Exact span hashes and guide lengths are in the receipt.

Neither PDF was inspected. Supplied helpers, builders, scientific data and recorded checks were not executed, imported, evaluated or independently recertified. The README commands and numerical check totals remain the authors' evidence descriptions only. External references, publication priority, asymptotic proofs outside the spans, and original ProveIt dependency proofs were not audited.

## 2. Lacunary iteration: a concrete digit-valuation interface

The manuscript studies F_p(x)=sum_(j>=0)x^(p^j) and A_p(m,N)=[x^N]F_p^(compose m). Its stated uniform divisibility theorem, at supported degrees N=1 mod(p-1), is

    v_p(A_p(m,N)) >= (s_p(N)-1)/(p-1),  m in Z.

In particular 2^(popcount(N)-1) divides A_2(m,N). The statement covers moving m as a valuation inequality. The separate constructive automaticity theorem fixes p, precision q and nonnegative iterate m. It constructs a finite Cartier representation for A_p(m,N) mod p^q, queried by reading the digits of N. The inspected dimension recurrence can grow rapidly with m and q. For supported N>1, a further stated sufficient coefficient period in the iteration parameter is p^(q-w+floor(log_p d)) when q>w, with d=(N-1)/(p-1) and w=(s_p(N)-1)/(p-1); it is explicitly not asserted minimal. The degree-one coefficient is identically one and is treated separately by the manuscript.

This is the stronger of the two arithmetic leads: it supplies a precise candidate interface for digit-weight divisibility filters and finite modular coefficient extraction. It may be relevant to the research program's population/prime-power conditions if an exact coefficient identity can be found. The manuscript's full valuation proof, composition closure, Cartier-module closure lemma and p-adic interpolation proof were not read in this reconnaissance, so their all-parameter correctness is not newly certified here.

**Boundary 1 (fixed iterate is not the diagonal automaton).** This limitation belongs to the authors, explicitly at lines1078–1082 and1338–1344 and in the README. Substituting m=N into a theorem that constructs a different representation for each fixed m does not provide one finite automaton for the diagonal. Nor is a uniformly inexpensive setup in m,q proved. The valuation theorem's moving-index scope must not be transferred to the narrower automaton theorem. This is not a discovered source defect.

**Open question 1 (native coefficient bridge).** The review-side arithmetic question is whether any useful native half-binomial coefficient Y_R, or another exact coefficient appearing in the actual compiler, is representable as an A_p(m,N) covered by the report, with all substitutions and losses controlled. No such identity or soundness transfer has been found or claimed here. Digit-sum resemblance alone supplies none. A paid variable-parameter coefficient evaluator would be an additional obligation, not a free consequence of a finite automaton for each fixed parameter.

## 3. Morphic words: exact positive compression with information loss

For a fixed word w beginning in1, containing a zeros and a-1 ones, the report considers sigma(0)=1,sigma(1)=w. Its complete-block proper-prefix histograms have the stated formula

    F_(2m,c)(t)=1+K_c(t) sum_(j=0)^(m-1) Delta(t)^j,
    Delta(t)=S(t)S(t^-1), c in {0,1},

with nonnegative integral Laurent coefficients. The selected proof derives the two-step matrix C(t), trace Delta+1, determinant Delta, and (C-I)(C-Delta I)=0. A later refinement displays a rank-one factorization of C-I and records the same positive identity conditioned on the next letter. This is an explicit low-rank positive recurrence, more concrete than a spectral approximation.

The algorithmic paragraph states linear support growth in m and O_w(m^2) integer coefficient operations, while literal substituted words have exponential length. It also states coefficient bit lengths O_w(m); it does not treat arbitrarily large coefficients as constant-bit objects. These interfaces suggest a special compressed counting or trajectory-statistic block. They do not by themselves implement arbitrary controlled histories or reduce our complete compiler's cost.

**Boundary 2 (histograms forget chronology).** The authors explicitly warn at lines1094–1099 that different admissible words can have the same profile and hence identical complete-block prefix histograms at every depth, despite differing internal prefix order; arbitrary-cutoff corrections may retain the lost information. This reported collision of representations is credited to their warning, not presented as a new reviewer counterexample. Thus full-block histograms cannot simply replace an exact ordered history wherever acceptance depends on the forgotten chronology. No broader impossibility theorem for morphic computation or augmented encodings follows.

**Open question 2 (finite-arity and operational bridge).** The review-side follow-up would need to identify a relevant acceptance predicate determined by these histograms, or add a paid order-recovery interface, and then encode the variable-depth Laurent polynomial with a fixed number of ordinary positive integer witnesses and fully charged arithmetic. The delivered fixed-substitution iteration and polynomial-array algorithm do not establish a fixed universal controlled alphabet, arbitrary-program/ordinary-input simulation, or that encoding. The authors separately pose higher-alphabet positive low-rank generalizations at2028–2035; their invariant-section mechanism alone is explicitly insufficient to establish the desired positivity. No solution of that question is claimed here.

**Review remark 3 (retained correction of the reviewer's period scope).** The first frozen review said: "A further stated sufficient coefficient period in the iteration parameter is p^(q-w+floor(log_p d)) when q>w," without specifying supported N>1. Root caught the omission during independent reading. At N=1, d=w=0, so q>w holds for every positive precision but log_p(d) is undefined; the actual coefficient is identically one. The manuscript itself states N>1 at line1183 and separates degree one at1212–1216. The corrected period sentence above restores that hypothesis. This is a correction to reviewer wording, not a source theorem error, and does not affect the all-N valuation statement. The original MD SHA74017e3e07ebcdc716cfe10426f620d7af48f71e4dae347c884a8348c7da19fb and JSON SHA2a90a6e4361bfc3721824e90d5d5a0b843b276c1fe9dad691ce6247be94b304d remain frozen unchanged.

## 4. Frozen scope

Priority is a bounded coefficient-identity investigation for the lacunary report, followed only if useful by a histogram-invariant experiment for the morphic report. The arithmetic connections above are reviewer inferences and proposed questions; the displayed theorem interfaces and limitations are attributed to the delivered manuscripts. No theorem flaw is asserted from this navigation, and no full-proof PASS is issued.

Only fresh byte/inventory/read-span metadata processing was performed. No supplied, archived, committed, predecessor or frozen program was run or imported; no saved scientific or source array was evaluated, no degree propagated, no build performed, and no Git fetch or repository mutation made. New outputs are confined to the retained first /tmp review pair, this corrected v2 pair and four authenticated manuscript/README text copies in /tmp/lacunary_morphic_interfaces_aristotle for independent inert reading. Earlier frozen reports remain unchanged.
