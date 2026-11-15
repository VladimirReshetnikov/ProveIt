# Pinned PA machine comparison

Snapshot: `VladimirReshetnikov/ProveIt@8d31445d858761a8f6150c2e5012adae8895e932`.
This is an independent structural inventory and a reconciliation of reported proof status. It does not claim that every historical mathematical proof or every checker was rerun.

## Scope and reproducibility

`audit_inventory.py` reads all 718 tracked `.tm` files beneath `Computability/BusyBeaver/Research/PA`, then every literal `.tm` member in the six current incoming ZIPs and all distinct recursively nested ZIP payloads. At this pin there are 2,826 literal occurrences: 718 tracked and 2,108 in incoming/nested archives. The strict recognizer accepts complete five-column binary tables with exactly one terminal label. It accepts 2,803 occurrences (855 distinct byte payloads); 23 occurrences fall outside that recognizer. Most exclusions are deliberate diagnostic tables with no terminal or several terminal labels, not purported consistency constructions. Their paths and reasons are retained in `census_all/rejected.json`.

For each accepted table, we compute every rooted breadth-first transition tuple (read 0 before read 1), the maximum graph-reachable count, and whether a root spans the whole graph. For a spanning table the lexicographically least complete tuple is a canonical form under arbitrary control renaming and arbitrary spanning initial root. The exact tuple, rather than an unequal byte hash, is the mathematical equality criterion; hashes name the resulting classes. Every 194-state spanning table also receives the stronger canonical form allowing tape reflection, global bit exchange, and erasure of actions entering halt. Bit exchange is solely a graph-novelty test; it does not preserve the specified zero-blank convention by itself.

No purported exact graph classification is assigned to disconnected diagnostics by truncating their unreachable components: they remain separate byte payloads in this fresh census. Declared initial states and dense-state-0 conventions are distinguished. In particular, the native-numbered HAZ tables can be densely numbered without state 0 being the intended start. Initial-state-specific rooted classes therefore remain separate metadata from unrooted graph classes.

The 87 filed packets' existing `MACHINES.tsv` catalogs 705 historical classes from 13,879 delivered `.tm` occurrences. The repository has removed repeated table files while retaining relocation metadata. That historical occurrence count is inherited from the pinned registry; the 718 extant files and the current incoming archives were freshly parsed. The complete new observed frontier has **139 spanning 194-state classes**, rather than the 110 of earlier reports, plus two nonspanning byte forms. There are **54 spanning 193-state research classes**; these must not be described as accepted blank-start consistency machines. All classes and occurrences are recorded in `census_all/`.

`audit_json.py` additionally examines common explicit table encodings inside every tracked PA JSON file and nested incoming ZIP JSON payload. Its reported scope excludes arbitrary unevaluated generators and prose-only tables. The completed JSON supplement read all 11,847 tracked/nested-incoming JSON occurrences (8,205 distinct payloads), with no parse errors. It recognized 311 explicit 194-table occurrences, 145 normalized labeled tables and 82 spanning classes; every class was already in the literal frontier. These results do not change the literal-file counts.

## New current deliveries and duplicate names

The six current outer ZIP payloads are distinct deliveries, but their claimed principal machines overlap substantially:

| Current delivery | Principal graphs | Relationship and proof claim |
| --- | --- | --- |
| `pa194_ax11gh_research_2026-11-14.zip` | AX11GH, AX11GHS | Four-field eleven-entry AX, explicit generalization binder, Q head orientation, visible no-push MP, cache-only Shift. Written relative iPRA proof importing current QAX11H absolute calibration. |
| `pa194_ax11gh_research_2026-11-14(1).zip` | Same AX11GH/GHS, plus AX11GHF/GHSF | F variants add two recurring three-to-one physical shortcuts. Direct relative iPRA acceleration proof, then the same inherited absolute calibration. |
| `pa194_research_2026-11-14.zip` | AX11QGH, AX11HR | AX11QGH is the same literal GH graph above. HR is a distinct nine-register physical allocation, with complete symbolic source contracts and shorter initialization. |
| `pa194_sel_ax11gh_research_2026-11-14.zip` | SEL, same AX11GH | SEL reorganizes two decoder pairs into history selectors and proves direct relative iPRA equivalence to primary PA194. This delivery expressly leaves the absolute primary calibration open. |
| `pa194_loop_continuation_research_2026-11-14.zip` | LC, LC_A, LC_B, LC_C, LC_AX11H | Five three-row loop-continuation implementations. Four preserve the primary source; LC_AX11H imports the revised AX11H written absolute theorem. Its GAX11 reproduction is already filed as AX11G and is excluded from the novelty count. |
| `pa_conpa_research_2026-11-14.zip` | Same AX11GH/GHS | Another delivery of the same two literal graphs, with expanded proof/census provenance. |

There are **11 distinct principal new graphs** across these deliveries: GH, GHS, GHF, GHSF, HR, SEL, and five LC graphs. The 29 fresh 194-state classes consist of those eleven and eighteen research auxiliaries/rejected scanner or selector modifications. Calling all 29 valid consistency machines would misstate the evidence.

The dense GH table has SHA-256 `513e9c8b28e0dd41e6003bb8d82c80ff3dac5fb3c5274cd2f709a3bba8c3e9e1`; GHS has `7a4738a9eedd3f53674d67568b3197d38237d11d0fc08fa3d41251a8faf8052c`. The GH name is ambiguous across history: PA194GH with ten-entry AX is a different earlier design from PA194AX11GH with eleven-entry AX.

## Mechanism families

The inherited named-design ledger separates twenty-two major families. Their component improvements are not automatically additive, because grammar readers and compatible contextual folds must be counted together.

1. **Original primary interface.** The 194-state designs use either 134 fixed + 67 readers − 7 folds or a different 68/8 arrangement. The resolved register program and blank initialization are separate correctness obligations.
2. **Formula coefficient changes.** Coefficients 4, 5, and 6 change every constructor. A sound comparison needs hereditary recoding and a proof for the dominated implication axiom; mere numerical monotonicity is insufficient.
3. **MP storage choices.** Cached-result C/CS, visible no-push N, and original dummy-push MP require different arbitrary-stack compiler invariants. No-push MP needs a reserved zero below its premises.
4. **Shift guards.** Original sum test `t+h=1` and cache-only `h=1` have different early-halting behavior. In the H family, a returned top-one contradiction must be detected using Pop; a single Shift can miss it.
5. **Comparator symmetry.** Reversing destructive comparison operands removes source restoration instructions. Source instruction savings do not necessarily remove a physical control after decoding and folds.
6. **Q distribution.** Exchanging the two curried universal-distribution premises changes the emitted numerical head. The restricted implication basis supplies a fixed premise-exchange proof; this is not merely a physical row permutation.
7. **Separate diagonal selectors.** Choosing Gamma(A) or Gamma(D) changes the selector proof and emitter associations; supplementary combinations sometimes have narrower verification than the principal machines.
8. **Known-zero routing.** A/F/J/ZR/R/CSZ/CZ/HA/HAZ replace jumps with zero-register decrements. A source invariant alone does not establish the exceptional blank startup.
9. **Physical register allocation.** AD, TDY, P5, HX, HR preserve abstract commands but reassign positions and entry routers. Exact full-tape frame conjugacy and startup are required.
10. **Decoder topology.** B, 4L, QH4L/QH4R, LC, and SEL preserve source behavior while changing repeated controller paths. These are the best candidates for direct local iPRA preservation proofs with explicit physical clocks.
11. **AX11 interface.** Four operands and eleven saved entries allow reuse of Push and full MP-reader fallthrough. The fourth AX field is real, cannot be omitted, and all eleven selectors must be treated.
12. **Explicit generalization binder.** G uses AX's first operand c in U(c,h), instead of the incoming offset. It shortens the generalization compiler word but still needs the exact arbitrary-store argument.
13. **Combined GH/GHS and F acceleration.** AX11, G, H, Q and no-push choices are combined with ordinary/symmetric comparison. F is an additional physical acceleration, independent of the PA logical calibration.

The fresh `current_frontier194_ledger.{csv,json}` annotates all 139 spanning classes. `current_all_literal_classes.{csv,json}` lists all 720 accepted spanning classes across sizes and seven nonspanning byte forms. `source_integrity.json` verifies all 724 tracked table/current outer-ZIP payloads against pinned Git blob identities. A machine-readable copy of the inherited 22-family matrix and 63 named-design ledger accompanies the fresh exact-class ledger. The annotations are attributed report claims; they are not new end-to-end proof audits.

## Proof-status reconciliation

The pinned PA top-level README says neither physical-machine-specific direction has been established in the formal iPRA development. This statement remains relevant to Lean. However, the latest incoming reports import a substantially expanded *written* AX11H mathematical calibration. It is inaccurate to summarize every latest delivery as claiming only a relative result.

The exact inherited AX11H ZIP has SHA-256 `93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075`. Its own source pin is `1c9524d8bf2e0a27b9a16ff622359927f536e663`, with Foundation submodule `32e1a0956a8622fad067328ca1959729a7634428`. Copies of that unchanged ZIP occur in the current GH/GHS, LC, and AX11QGH/HR deliveries. The written theorem is for the inherited `nativePAConsistency` predicate, with the exact Foundation proof encoding and adapter documented separately from the Cantor numerical calculus.

The main dependency chain is literal table ↔ primitive source ↔ abstract scheduler ↔ numerical refutation ↔ Foundation PA refutation. The new written calibration supplies explicit positive primitive-recursive simulation clocks; arbitrary gap/spare-list frame parameters; bounded-store compiler induction; a finite-demand proof-construction scheme using decreasing source ranks; term/equality/induction suppliers; and an adapter between historical PAeq and current Foundation PA. Its proof sources distinguish quantifier-free or Sigma1 induction from invalid unbounded all-store induction. Neither its full numerical PA-proof compiler nor the complete theorem has been freshly implemented and kernel checked by those finite certificate scripts. It remains an identified written mathematical dependency subject to independent review.

Consequently, a new low-level table can honestly assert a directly established relative iPRA theorem, and obtain the absolute consistency corollary by explicitly invoking that written AX11H calibration. A report must not say Python replay alone proves the arithmetic equivalence, or that an end-to-end Lean proof has been completed. If the new result instead relies on the original primary table alone, its absolute iPRA calibration is not supplied by the newest AX11H theorem without a proved connecting equivalence.

## Why the 193-state entries are not solutions

The most substantive inherited 193-state core identifies native control 301 with 88 and changes `88/0` to `0 L 51` and `51/0` to `0 R 122`. It implements all 4,780 source outcomes on complete encoded runtime frames. It does not initialize correctly from blank: the unchanged native start74 reaches an outward ray, and every merely changed initial control also fails the tested startup criterion. Reusing its runtime certificate while ignoring the startup would be an invalid reduction.

The corrected startup-repair pool has327 individually screened edits; nine edits of35/0 from an earlier incorrect context envelope were removed. Prior work screened eligible pairs and triples, and all-start triple search reached resource limits in255,752 runs. Those cases are not proved impossible. Four-or-more adaptive edits, another initialization invariant, and a jointly synthesized scanner/startup interface remain outside that restricted negative result. A startup hit is only a proposed machine until all source contracts are checked again simultaneously.

## Strongest remaining directions

- Combine formally justified incoming-row shortcuts with decoder continuation/history transformations, then seek elimination of a shared physical control. This targets genuinely new transition neighborhoods rather than repeating direct contractions on old tables.
- Jointly synthesize blank initialization and the proven193-state runtime splice. Search only complete finite-support frames, with explicit source entry and positive runtime clocks.
- Change a logical schema or command interface enough to lower the fixed+reader−fold total; a shorter source expression alone is not sufficient. Every changed logical family needs actual proof translations.
- Treat ZFC folds as source-engine hypotheses: the shared marker mechanism explains the193-state splice, but the PA blank initializer has an exceptional read-zero use that invalidates direct transplantation.
- Use DiophantineConsistency and ConciseIPRA chiefly for proof-predicate adapters, weak-arithmetic witness transformations, and proof-checker design; none of their compact descriptions automatically yields a small binary blank-start tape implementation.

## Late freshness check

A separate addendum checks later revision `ef0839bf15d8b556bc1e1634e6ad310adbcd4fe3`. The six incoming archives have been filed; all 42 newly added literal table payloads already occur in this pinned census, and the 139-class frontier is unchanged. New formalization files cover specific model-logic and partial/conditional simulation components; they do not claim a completed machine-specific consistency theorem. See `LATE_ADDENDUM.md` and `late_addendum.json`.

## New bootstrap experiments

The present audit also ran four adaptive encountered-row beams on the inherited Runtime193 and AX11 Runtime193 cores. They performed 767,923 candidate simulations and 65,104,852,630 literal transitions; 709,278 runs involved at least four edits. Three beams completed depths 12, 16 and 12; the final growth-prioritized beam completed depth 13 and part of 14 before its wall budget. No whole-source-frame hit occurred. The 693,876 resource-bound stops remain unresolved. Counts overlap across experiments, so they are execution-work totals rather than distinct machines. Search code, exact inputs, positive control, source-template binding, logs and per-depth receipts are in `../research/startup_search/`. No state-count lower bound or simultaneous runtime-preservation claim is made.
