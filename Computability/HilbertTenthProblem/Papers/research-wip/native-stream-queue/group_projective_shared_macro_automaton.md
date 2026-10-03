# Shared macro continuations in the complete projective compiler

The actual three-code fixture `(1,1,2),(2,3,2),(4,5)` admits a complete **230=98M+132A** one-kernel projective source, with **33 positive witnesses, six comparisons and exact degree1789**. The explicitly emitted private-path baseline costs **236=99M+137A**, with34 positive witnesses and the same six comparisons and degree. Thus this bounded transfer saves **six operations, 1M+5A, and one witness**. Both sources retain the ordinary affine input and the original height constructor.

These are complete sources in the latest product-radix/tail-quotient architecture, not standalone controller ledgers. The fixture is not asserted universal, and230 is not a numerical universal bound. The graph construction and native interface argument apply to fixed macro tables; instantiating a universal alphabet still requires its actual numerical table. The comparison is between the two explicit schedules saved here, not a claim of globally minimal private-path packing or arbitrary-graph flow.

**This particular fixture has an empty positive-input projective language.** It uses only letters1 through5, so the fourth signed coordinate never changes from u=24x+13≥37 and cannot reach the required final value1. The fixture is an arithmetic source benchmark, not a nontrivial accepting example. The shared-controller construction and its native interface proof remain applicable to branching tables; a nonempty or universal numerical benchmark requires a different actual table.

[Source](group_projective_shared_macro_automaton.py) and [receipt](group_projective_shared_macro_automaton.json) are a standalone standard-library, pinned CLI. They reconstruct literal saved source blocks and run no historical builder or historical verification suite. All predecessor bytes remain unchanged.

## 1. Fixed physical language, nonidle edges and lanes

The fixture is the named original regular-controller example already authenticated in [the shared-macro packet](group_macro_automaton_sharing.md). Its private controller uses eight nonidle edges and five internal states. The prefix/suffix construction identifies the common final letter2 of the first two codes, giving seven nonidle edges and four internal states. Number the shared nonidle edges as follows:

| Edge | Source | Target | Letter |
|---:|---:|---:|---:|
|1|0|2|1|
|2|0|3|2|
|3|0|4|4|
|4|1|0|2|
|5|2|1|1|
|6|3|1|3|
|7|4|0|5|

The distinguished hub0 and equal-continuation proof preserve the entire labeled macro language. Here both circuits use the existing [idle-free projection](group_projective_idle_free_paths.md): no idle hat is supplied, `J=sum(Ehat_e−1)`, and every actual transition is a nonidle edge. The old and new edge lists accept exactly `({code_1,code_2,code_3})*`. A complete subset-state equivalence decision checks the two literal lists in the receipt.

For an accepting projective computation, the empty word cannot take `(1,u,1,u)` to `(0,1,0,1)`. Therefore an actual accepting word has positive duration. Conversely all hub identity steps may be removed without changing this endpoint action. This uses the existing idle-removal theorem, not a new assertion that a zero-duration history satisfies the certificate. Arbitrarily large dyadic height remains available for every accepted positive-duration word; padding by additional idle steps is unnecessary.

The latest compiler already reindexes only nonidle edges. Hence both n=8 and n=7 use **m=8** lanes. There is no m16→8 saving here, unlike the earlier two-kernel packet. Every state label is below8, and every chosen packing map is an injection into positions0 through7.

The chosen private schedule uses positions `[0,1,2,3,5,4,6,7]` for its original private-path edge order. The shared schedule uses `[5,6,3,1,0,2,4]` in the table above. Physical actions and chronological cell order are never permuted; these positions select storage lanes only.

## 2. Actual source reconstruction and paid graph interface

The starting template is the complete saved m8 `source_example` of [label-aligned lanes](group_projective_label_aligned_lanes.md), including its full seventeen-gate finalizer. It has the same native and projective interfaces required here. The source authenticates that template, copies its graph-independent instructions, and regenerates every graph-dependent consumer: J, four signed physical-selector differences, the physical selector pack S, controller word C, and both weighted flow sides. It retains all eight selected-source hats, all four history fields, the global bound, and every native positive coordinate.

The unchanged five-row ordinary-input/height prefix is exactly

    input_product = 24*x
    u = input_product + 13
    D = u + height_slack
    c0 = D - 1
    B = 16*D.

In particular height_slack is still a supplied positive coordinate, and no direct-D projection is made. For x>0, u≥37 and D>u, so B>m independently of every comparison.

The static template receives precisely the already proved [product-scale](group_projective_product_radix_scale.md) edits: the top mask multiplication uses2, `q=32*range_Bshift`, and the private old scale product is deleted. It also receives the [tail quotient](group_projective_tail_quotient_shift.md) edit `w+packed_z_product` in place of `w+packed_top_sum`. The resulting paid scale is

    P=(B−1)J+1,  T=P^16,  T2=P^24,  q=32B*T2.

All powers, products, folded truth ports and native factors are literal paid rows. No runtime power or AND operation is added to the instruction set.

For E_e=Ehat_e−1, the regenerated scalar interface is exactly

    J = sum_e E_e,
    dS_i = sum_(label=2i+1) E_e − sum_(label=2i+2) E_e,
    S = sum_e E_e P^(label_e−1),
    C = sum_e E_e P^(position_e),
    flow_left = sum_e source_e E_e,
    flow_right = B*sum_e target_e E_e.

The private baseline uses the guarded disjoint-path flow identities, including reuse of its internal-plus-first checksum sum. The new graph uses a general grouped target/source-weight computation. It does not invoke the disjoint-path incidence-one formula. Fixed weights, hat offsets and every new sum or product are charged. Literal zero/one propagation and exact repeated gates are explicit; only private dead instructions are removed, and all supplied coordinates remain live.

The shared winning packing has a short independently checked identity. With E1,E2 the first two edge fields in the table,

    C = S + (P^5−1)*(E1+P*E2).

All other edges occupy their physical label-minus-one lane. This identity moves those first two fields to lanes5 and6 without changing S. The source pays the P5 producer, the factor subtraction, the hatted inner sum and its offset, the product and the final addition. It is not an uncharged lookup or a field permutation on the physical trace.

## 3. Noncircular positive soundness on the branching graph

The full output has exactly the inherited form

    F = U*(1 + R0²+R1²+R2²+R3²+Rflow²) − 1,

where U is the product of the seven native/joint units. At a positive integer zero, every outer residual vanishes and every unit factor is ±1. The joint bound factor is

    L = G−P,  G=sum_i H_i + sum_j Zhat_j + global_slack.

For either sign of L, all supplied positive fields give P≥12, each H_i<P and each Zhat_j−1<P. Since J is a sum of nonnegative E_e, the literal identity P=(B−1)J+1 now excludes J=0 and yields J≥1 and B≤P. No path, bit or power conclusion has been used.

Each E_e≤J. The physical selector coefficients are nonnegative sums of these E_e and are at most J. Distinct controller lanes therefore give `0≤C≤J R8(P)<P8`. The physical mask coefficients `(B−1)*S_j` are at most P−1, before Boolean typing. The range-mask coefficients `(2D−1)J` are also less than P. Thus all three lower physical/controller/range regions satisfy the same scalar bounds as the product-scale parent. Neither a unique edge incidence nor disjoint macro paths enters this argument.

Let H,M,Z be the complete joined words. Their top blocks remain `B*T2` and `2*T2`, and the lower regions are below T2. With Q=q/16=2B*T2, the reconstructed native fields are

    F0=16(Q−H−M+Z)−15,
    F1=16(H−Z)+4,  F2=16(M−Z)+2,  F3=16Z+8.

They are strictly positive, sum to q−1, and have the original fixed residues1,4,2,8 modulo16. The retained odd quotient, ratio slacks, native units and tail quotient therefore meet exactly the [tail-shift bootstrap](group_projective_tail_quotient_shift.md#2-pretyping-bounds-replacing-the-old-x-bound). Its recovery handles both potential index signs before deriving the old positive quotient. The proof depends on these scalar fields and low-bit classes, not on the controller's path incidence. No old `X>r` hypothesis is assumed prematurely.

That native recovery makes q dyadic, restores all native units to1, and consequently L=1. Because `q=32B*P24` with positive B,P, both B and P are dyadic. The repunit identity yields a common positive duration, P=B^t. The separated joined AND then types every E_e as a Boolean radix-B word. The checksum and B>8 force exactly one selected edge per position.

Both weighted state words have digits below B. Their equality `source_word=B*target_word` gives source0 at the first position, target0 at the last, and chronological adjacency between each pair of consecutive positions. This conclusion is valid on the branching shared graph. Its recovered physical word belongs to the same macro language. The other AND regions type selected sources and enforce history digit bounds. The unchanged initial height inequality D>u and four signed transports then recover the genuine projective computation and required paired endpoint.

Thus any new positive zero accepts precisely the same ordinary-input predicate as the fixed macro construction. All compiler conditions are retained; arbitrary off-zero negative computed differences do not introduce additional domain restrictions.

## 4. Positive completeness and equivalence scope

Conversely take an accepted macro word at the given x>0, remove its hub idle steps, and choose a path in either graph. Its nonempty word has some finite positive duration t, with no external horizon fixed in the source. Choose a sufficiently large dyadic D greater than u and one plus every absolute state coordinate of that word. Set height_slack=D−u>0, B=16D, P=B^t and the true J.

The true shifted histories, edge hats and selected-source hats have the same positive scalar margins as the existing projective converse. The different injective lane pack is a subset of the same full eight-lane origin mask. All low, controller and range AND predicates therefore hold. The product-scale prescribed native converse supplies fresh positive auxiliaries at the actual q and packed index; the proved tail coordinate map gives the new quotient. All six comparisons and the complete finalizer are satisfied.

This establishes equality of the existential ordinary-input relations. The two graphs have different edge witnesses, and repacking changes the native fields and index. No same-tuple polynomial identity or full positive-zero bijection is asserted across graphs, across different lane maps, or between the new scalar scale and its older ancestor. For fixed graph and fixed lane map, the alternative packing expressions do have the exact same polynomial; the helper proves their common complete interface rather than using equality only at zeros.

## 5. Complete ledgers and degree

| Explicit source | Certificate | Full polynomial | Positive witnesses | Comparisons | Exact degree |
|---|---:|---:|---:|---:|---:|
| Private-path baseline |219=93M+126A|236=99M+137A|34|6|1789|
| Shared graph |213=92M+121A|230=98M+132A|33|6|1789|

The finalizer remains seventeen paid instructions: five residual subtractions, five squares, four sum additions, addition of1, multiplication by U and subtraction of1, totaling6M+11A. Its operands are only renamed to the proved flow ports. Every supplied coordinate and every surviving gate reaches the full output.

The bounded source choice is explicit: five distinct lane maps per graph, each with direct padded-hat Horner packing, a per-edge correction to S, and grouped-offset corrections to S. The original consecutive placement is included. The private graph uses its valid specialized shared-checksum flow, while the shared graph uses general weighted flow. The receipt records all30 actual ledger/source hashes and saves both complete winning arrays. It does not claim exhaustive lane permutations, arbitrary arithmetic circuits, or the best possible historical compiler schedule.

Ordinary degree propagation gives the conservative bound1839. At the actual checked main-norm cone, use the all-value identity

    (X+ac+gamma)^2−(a²+4a+3)c²
      =X²+2Xac+2Xgamma+2acgamma+gamma²−(4a+3)c².

The helper verifies every producer before this cancellation; no zero equation is used to reduce degree. Here m8, computed P, a_scale24 give `deg q=49`, `deg F3=47`. The seven resulting unit degrees are

    first247, main442, auxiliary308, index196,
    linear196, strong392, joint2.

Their sum is1783; the largest outer residual degree is3, giving the guarded full upper1789. For every actual emitted schedule the helper also propagates the coefficient of that precise top degree after substituting each free coordinate by its recorded positive weight times an indeterminate, modulo1000000007. The full degree1789 coefficient is nonzero. Consequently the upper bound is attained by the actual fixed-numeral polynomial. This is an exact-degree certificate, not a fit to sampled numerical values. All supplied coordinates, including x, have degree1; fixed24,13 and all other compiler numerals have degree0.

## 6. Reproducible source evidence and limits

Authentication covers the saved template, product-scale and tail predecessors, macro-sharing source, relevant native proof notes, and the exact sparse-flow/packing antecedents. Replay imports no historical compiler modules and executes no historical builder or suite.

The checker proves **270 exact coefficient identities** for the nine complete graph ports across30 sources. It then substitutes those proved ports into the literal static template and checks **5,490 complete retained-register expressions, all180 comparisons and every whole output**. It checks all **7,239 paid live gates**, all30 exact-degree certificates, and360 complete evaluations including120 rational cases. These are ring-polynomial/interface checks, not a claim that arbitrary rational zeros have the positive-integer semantics.

A further **78 genuine physical outer histories** traverse nonempty macro words in the two actual graphs. They keep the original ordinary input/height prefix, verify the full product-scale AND and all four positive truth fields, restore the positive global slack, and check every chronological flow equality. The actual endpoint defect of each history transport is checked as P times the difference between its true final coordinate and the required target. These control words are not claimed to reach that target, and no full native Pell zero is materialized. Unbounded completeness comes from the parametric theorem, not these finite examples.

Run from any working directory:

    python3 group_projective_shared_macro_automaton.py --root /absolute/path/to/native-stream-queue --expect /absolute/path/to/group_projective_shared_macro_automaton.json

Use `--output` to write the deterministic receipt. The helper is a bounded pinned compiler/verification CLI, not a maintained hostile-input API. The height constructor remains unchanged, and no direct-height projection, auxiliary elimination, external duration bound or numerical universal alphabet is included.
