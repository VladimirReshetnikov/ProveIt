# A shared finite macro controller with a complete paid matrix source

For the actual three-code fixture in `group_regular_macro_controller.py::verify`, sharing identical macro continuations reduces the complete shared-typing matrix polynomial from **443 = 179M + 264A** to **414 = 169M + 245A**. These counts include every ordinary-input, history, controller, native typing, geometry and endpoint condition, and the complete sum of 47 squares. The comparison circuits alone cost **303 → 274**. The change saves **29 operations = 10M + 19A** and **eight positive witnesses**, from 83 to 75.

This is a source-level reduction for one named fixed controller and a general finite-controller construction. The three-code fixture is not a universal subgroup alphabet. In particular 414 is not a new numerical universal bound. The more recent one-kernel/projective compiler is not modified here; transferring this arbitrary-graph controller to its additional interfaces is a separate obligation.

The [source](group_macro_automaton_sharing.py) and [receipt](group_macro_automaton_sharing.json) are a bounded standard-library CLI packet. They read authenticated saved sources rather than running historical compiler builders or test suites. One isolated authenticated historical path-flow planning fragment is executed only to obtain the fair specialized baseline. No maintained general public API or hostile-certificate interface is claimed.

## 1. The actual fixed language and its smaller controller

The authenticated original fixture is

    code_1 = (1,1,2), code_2 = (2,3,2), code_3 = (4,5).

It is the fourth `examples` entry in the original regular-controller verifier. The physical letters 1 through 8 are the original signed unit shears, and letter 0 is the identity. The required physical language is

    (0 | code_1 | code_2 | code_3)*.

The old construction has a distinguished hub 0, a hub identity loop, and disjoint paths for the three codes. Its nine active edges pad to **m=16** with duplicate hub identity loops. Its five internal states are distinct. The shared construction has four internal states and eight active edges, already **m=8**:

| Source | Target | Physical letter |
|---:|---:|---:|
| 0 | 0 | 0 |
| 0 | 2 | 1 |
| 0 | 3 | 2 |
| 0 | 4 | 4 |
| 1 | 0 | 2 |
| 2 | 1 | 1 |
| 3 | 1 | 3 |
| 4 | 0 | 5 |

The final letter 2 of the first two codes is one shared transition. This merges equal continuation languages rather than identifying merely equal physical labels. Every state code remains below m. Renaming nonhub states to make frequent weights cheap changes neither paths nor their physical words.

The general construction first builds a proper-prefix trie. A final letter returns directly to the distinguished hub; a nonfinal letter goes to its longer prefix. If one code is a prefix of another, both a returning edge and a continuing edge with the same label are retained. No epsilon edge or premature reset is introduced. Empty codes may be removed because the empty word is already accepted; duplicate codes do not change the language. The identity hub loop is always retained.

Process proper prefixes in decreasing length, assigning the same class precisely to states with the same set of pairs `(physical label, successor class)`. The hub is never merged with an internal state. Proper-prefix transitions are acyclic, so these signatures are well defined. Equality of signatures gives a labeled bisimulation: a transition in either representative has a transition with the same label to the same successor class in every other representative. Thus quotient paths can be lifted step by step, and original paths project. The accepting hub is distinguished in both directions. The trie itself accepts exactly concatenations of complete codes and hub identity steps. Therefore the quotient accepts exactly the original macro language, including its empty word and all identity padding. Uniqueness of a parse is unnecessary.

The checker also decides full NFA equivalence for the emitted fixture by exploring every reachable pair of subset states; it reaches seven pairs. This is an exact finite-automaton decision, not agreement only up to a selected word length. Eight additional boundary languages cover empty codes, duplicate codes, prefix-related codes and shared prefixes/suffixes. The general language theorem is the construction argument above.

## 2. A fully paid flow adapter for a branching graph

The old [sparse macro flow](group_sparse_macro_flow.md) planner requires the special incidence structure of disjoint paths. That premise fails in the shared graph, so the new graph uses a general adapter.

For a fixed edge `e=(a_e,b_e,label_e)`, supply its positive hat `Ehat_e` and abbreviate `E_e=Ehat_e-1`. The two exact scalar words are

    Aword = sum_e a_e*Ehat_e - sum_e a_e,
    Bword = sum_e b_e*Ehat_e - sum_e b_e.

The paid chronological comparison is

    Aword = B*Bword.

Every grouping is an ordinary integer-polynomial identity. The adapter groups hats by source or by target state, reuses those sums in the already required hatted checksum, pays every remaining sum and every nonunit fixed weight product, and selects the cheaper of those two emitted schedules. Literal zero and one operations are explicitly simplified, and exactly equal gates may be shared. There is no assumption of unique incoming or outgoing edges. The checksum still pays exactly m−1 additions for its left side, together with its separately charged right side `J+m`.

At a complete positive zero, the inherited scalar checksum and native subset theorem give Boolean length-t edge words with exactly one selected edge per radix-B position. Since every state code is below m and B>m, both flow sides have canonical digits. Equality therefore gives source 0 at the first position, target 0 at the last, and each next source equal to the preceding target. This proves actual chronological adjacency and both accepting endpoints even on the branching graph. Physical selector ports are the unchanged sums over edge labels.

In all five emitted sources the radix-margin instruction remains literally

    16 + controller__radix_beta = B.

Thus the original positive beta coordinate and the original threshold B>16 are preserved even when the graph shrinks to m=8. The general construction may use any fixed paid margin M≥m. Here only edge hats, checksum, packing length and native joined scale use the new m. We do not claim an unchanged positive interface after silently weakening the original radix margin.

## 3. The complete matrix relation and positive proof order

The unchanged [shared-typing source](group_shared_typing_matrix_compiler.md) supplies the full interface. The ordinary positive input is still x, with its paid literal prefix

    r = 24*x + 12,
    L_r = [[1+r,1],[-r^2,1-r]].

All original history endpoints, the target `diag(L_r,L_r)`, the selected-history lanes, and linked binary geometry remain in the source. There is no free input word or uncharged loader. The physical letter order and matrix-action convention are unchanged.

The source retains the 47-gate canonical history block, the 126-gate shared selector block, and the 47-gate geometry block from the authenticated saved empty-controller template. It reconstructs all controller-dependent instructions from the actual edge list. It also updates the two operands of `joint_Pm` to the actual last controller power, paying its multiplication. Hence the joined native kernel has the required new scale `16*P^(m+8)`, not the old m=16 scale with eight hats silently removed.

Soundness follows in the same noncircular order as the complete shared-typing proof. Positive hats and the scalar checksum first bound each edge word by J. The physical-port scalar sums bound selectors before Boolean semantics. Linked geometry recovers dyadic B, and the native joined AND projection recovers the required power and separates its two regions using those scalar bounds. The controller subset then types the one-hot edge words. The general flow equation above recovers a hub-to-hub path, whose physical word belongs to exactly the original macro language. The unchanged lower AND region types selected sources. Canonical history reconstruction and the one-vector faithfulness lemma finally give the target matrix product.

For completeness, take an accepted macro word for the given x and choose a path in either controller. Append hub identity steps until the inherited requirements t≥2 and B=8*4^t>16 hold. Set q_geom=2^t, P=B^t and the actual repunit J. Construct the genuine positive shifted histories and their bounds, edge hats, physical selectors and selected-source hats. Set the unchanged radix beta to B−16. The separate geometry theorem and the prescribed shared-AND theorem supply fresh positive native extensions at their actual scales. Their private coordinates remain disjoint. The proof in the [complete matrix compiler](group_complete_matrix_compiler.md) therefore applies to arbitrarily long accepted words.

Consequently the two complete sources represent the same existential ordinary-input relation. Across the two different graphs this is not a polynomial identity or a bijection between full supplied zero tuples. Hat counts and native scales differ, and fresh native witnesses can be needed. The exact polynomial identities recorded below apply only to alternative flow schedules on the same fixed graph. The preserved hub identity is both an accepted empty-product convention and the required arbitrary padding mechanism; no new halt transition is omitted or assumed.

## 4. Full literal counts and current metadata

Every form has 47 comparisons. The explicit finalizer pays 47 residual subtractions, 47 squares and 46 summation additions: **140 = 47M + 93A** operations. All supplied auxiliaries are strictly positive; computed differences need not be positive away from zeros.

| Graph and flow schedule | m | Comparison source | Complete polynomial | Positive witnesses | Degree upper bound |
|---|---:|---:|---:|---:|---:|
| Disjoint, original dense | 16 | 352 = 158M+194A | 492 = 205M+287A | 83 | 304 |
| Disjoint, general adapter | 16 | 306 = 134M+172A | 446 = 181M+265A | 83 | 304 |
| Disjoint, old guarded path adapter | 16 | 303 = 132M+171A | 443 = 179M+264A | 83 | 304 |
| Shared, dense | 8 | 292 = 132M+160A | 432 = 179M+253A | 75 | 208 |
| Shared, general adapter | 8 | 274 = 122M+152A | 414 = 169M+245A | 75 | 208 |

The fair old path-specific baseline is included explicitly: the new graph saves 29 operations against that 443-operation source, not only against the unoptimized dense source. Applying the general adapter to both graphs gives the independent comparison 446→414. The physical-port sum cost is p=5 for the disjoint graph and p=4 for the shared graph. The general flow blocks cost 19 and 15 gates respectively; the actual old guarded path flow costs 16 gates. Each checksum is paid separately as described above.

For the general adapter, if its flow block costs g=g_M+g_A, the full comparison-source count is

    (m+2h+101+g_M)M + (2m+h+p+121+g_A)A,

and the complete polynomial costs

    (m+2h+148+g_M)M + (2m+h+p+214+g_A)A
      = 3m+3h+p+362+g.

Here m=2^h and the native, geometry and ordinary-input blocks are the frozen shared-typing ones. These are counts of the explicit schedules, not an optimality claim for general automata or matrix certificates. The receipt records fresh literal upper degree bounds in all supplied coordinates with fixed compiler numerals of degree zero; this packet does not require a separate exact-degree assertion.

## 5. Source evidence, authentication and limits

The receipt saves all five complete source arrays, finalizers, comparison lists, auxiliary lists, edge tables and current ledgers. It authenticates all twelve referenced source/proof predecessors by SHA-256 before use. The named original fixture is recovered from the pinned verifier AST. For the fair specialized baseline only the pinned `groups` function and the initial planning fragment of `rewrite_controller` are isolated and executed; its disjoint-path guards remain in force. No historical module is imported, and no historical full compiler or suite is rerun.

Exact sparse coefficient checks prove all twelve controller residuals for every emitted form against its same-graph dense source: **60 residual identities** in total. They also check the three live controller outputs crossing into the selector block, including the complete packed edge word and mask: **15 exact cuts**. The remaining 220 instructions per form and the other 35 comparisons are literally identical. Induction through these identical downstream rows proves equality of all 47 residuals and the complete SOS over every commutative ring for each same-graph flow rewrite. The comparison of different graphs is the language theorem, as stated above.

The checker additionally verifies all **2,227 paid live polynomial gates**, source closure and every supplied port; performs **40 signed numeric whole-source comparisons**; and builds **415 genuine positive controller outer interfaces** on 83 physical words, including all-idle words, code concatenations and hub padding. Those outer fixtures check all twelve controller comparisons and the actual packed subset predicate. They do not assert a matrix target for those words and do not materialize either large native Pell zero. Unbounded matrix-language soundness and positive extension come from the parametric proofs, not these finite fixtures.

Run from any working directory:

    python3 group_macro_automaton_sharing.py --root /absolute/path/to/native-stream-queue --expect /absolute/path/to/group_macro_automaton_sharing.json

Use `--output` to write a deterministic receipt. Replay compares recursive exact JSON types as well as values. All historical predecessors remain unchanged. An instantiated universal alphabet, a transfer into the later projective kernel, and any further exact coefficient factoring are separate future source obligations.
