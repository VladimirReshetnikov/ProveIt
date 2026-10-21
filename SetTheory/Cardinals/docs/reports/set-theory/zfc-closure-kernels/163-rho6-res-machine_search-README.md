# Bounded searches for an additional state saving

These files record independent negative experiments on the accepted 217-state table and several checks on the new 216-state parameter variant. They do not prove a lower bound, and finite source-frame samples do not prove a positive machine equivalence. The supplied 216-state construction is established separately by its source proof, quantified runtime contracts, and complete blank initialization.

## Arbitrary two-row state quotients

`quotient_search.cpp` examines every unordered pair of working states. It merges the larger native label into the smaller label and allows both surviving transition rows to be chosen freely. There are 23,436 state pairs and 40,684,896 individual row specifications. The algorithm first screens one unknown row while treating a visit requiring the other unknown row as an unresolved obligation. It then tests every remaining compatible pair of rows with both rows fixed. Recursion through the merged state is permitted.

Each test compares positive old and new execution fragments on a 15-cell tape window. A successful local comparison requires the same complete window contents, head position, and state after applying the proposed quotient. The old endpoint may occur later than one step. A run that leaves the known window is rejected; the fuel cap is 97. Thus the search is deliberately local and bounded.

The source-only sample contains 76,355 distinct windows and covers all 434 transition rows. Its generator samples 18,513 source frames respecting the inductively checked source constants, lower bounds and joint zero/nonzero patterns, with gap 80 or 82 and 130 spare values all equal to one. It excludes the old blank prefix, so it does not unnecessarily require a new machine to reproduce that exact initialization. No quotient survived. A separate run including the complete old blank prefix likewise had no survivor.

## One shared selector and two deleted states

`shared_selector_search.cpp` allows a pair's replacement rows to enter a new selector, and synthesizes the selector's rows from existing transitions. It treats both original branches independently, so the family includes pairs with no common inherited branch. Its constituent local paths must meet an old positive endpoint before executing another changed keeper row. The source-only run screened 325,479,168 selector-row specifications and found 4,117 indirect branch families. Together with direct branches these yielded 40 complete one-deletion/one-addition families, covering 28 distinct state pairs.

No two complete families shared both selector rows, even after quotienting their targets. Both disjoint two-pair quotients and overlapping three-to-one quotients were considered. Replacing an existing helper state with one of these selector choices was also tested against that state's original source contexts: all 185,115 mutations were rejected. The compact 40-family record is included as `selector_variants.json` and `selector_variants.txt`.

## Unreachable source replacements

The source invariant proves three primitive ordinals unreachable. Their maximal subtrees have prefixes `11101001011001101` and `111111001`; they contain respectively a CC2 leaf and the pair (CI6, CC2). Replacing either or both by any of the 203 original subtree types explores 406 single replacements and 41,209 paired replacements. Open and otherwise irrelevant junk types were allowed in this purely structural count. The minimum remained 203 distinct DAG nodes. This is a statement about the enumerated replacements, not about all equiconsistent source programs. `python3 dead_subtree_search.py` reproduces the census from the included compressed baseline source. The script trusts the identified dead prefixes; it does not itself establish their unreachability. The source invariant is included separately as `source_invariant.json.gz`.

## Checks after the upstream 216-state publication

During the session, upstream commit `e6083665c6826e3a8aef969a8a4a8bc9031bd32b` published the 216-state partial-selector saving. The separately delivered parameter variant composes an independently found rho6 parameter permutation with that upstream construction. The state-count saving must be attributed to upstream. Additional existing-helper searches using all-tape predecessor-write invariants of lengths 2 through 8, two-cell shared helpers, and a bidirectional six-cell helper family found no 215-state successor. A further 150-second partial-selector source search tested 10,489 reparses inside the preserved live block [466,4574), targeting three additional read-zero pairs. Its best source had 204 DAG nodes, so it produced no 215-state candidate. These checks are distinct from the successful universal verification of the supplied 216-state variant.

## Reproduction

All C++ sources use only the standard library. For the quotient search:

```sh
gzip -dc source_context_input.txt.gz > source_context_input.txt
c++ -O3 -std=c++17 quotient_search.cpp -o quotient_search
./quotient_search source_context_input.txt > quotient_survivors.txt
```

The output survivor file should be empty; the final diagnostic reports 23,436 pairs, 40,684,896 row specifications and zero folds. The compact input starts with the number of working states and their native labels, then two transition triples per state. Transition targets use compact indices; the index immediately above the working-state range is halt. Each state's window list follows, with its count first. Window bit 0 is head minus seven and bit 7 is the current head.

For helper synthesis, compile `shared_selector_search.cpp`, pass the same compact input, and save its standard output as `allbranch-options.txt` beside the scripts. Running `python3 combine_selector_families.py` then reconstructs the 40 complete families and reports zero compatible double-fold candidates. For the existing-state reuse check, compile `reuse_selector_search.cpp` and pass the input followed by `selector_variants.txt`. Machine/source/input hashes and exact census totals are in `results.json`. The negative results remain tied to these bytes and to the explicitly stated bounded search families.
