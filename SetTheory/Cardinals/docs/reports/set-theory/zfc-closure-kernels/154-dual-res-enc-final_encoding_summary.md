# Encoding experiments and replay bundle

No experiment in this bundle constructs a machine below the repository's new 219-state baseline. Two alternative 219-state MP implementations passed the full symbolic runtime checker and complete blank startup replay. Other positive results are an exact family of native-code isomorphisms and a 13-instruction inverse decoder whose deliberately inaccurate membership case is permitted by the accompanying consistency argument. The latter is a reusable source component; its full detachment source increased the decoder DAG and is not a small certified machine.

The detailed mathematical and experimental account is `final_encoding_summary.tex`; the inverse-decoder arithmetic proof is `inverse_mp_research.tex`. Both are LaTeX sections intended for inclusion in the main report. The JSON receipts distinguish source counts, compiled decoder counts, finite tests, and unbounded proofs.

## Recorded searches

| Search | Exact scope | Result |
|---|---|---|
| Constructor prefix codes | All ten four-leaf binary prefix codecs with implication's zero code and membership's code 1 fixed; 707 selected source layouts | Original balanced codec best; alternative minimum DAG at least 209 against K220's 208 |
| Original logical rows | All 6^8 fixed-shape parameter-register layouts |208-node minimum twice; retained compiler minimum 220 |
| Reversed equality-existence atom | All 6^8 layouts with only `Ex_a E(a,b)` changed to `Ex_a E(b,a)` |209-node minimum; retained compiler minimum 222 |
| Global pairing mirror | Four unpair associations times twelve pair associations |All 48 have 212 nodes against K220's 208 |
| Global dyadic pairing | Nine pair layouts and two arrangements of each input-specific unpair routine:36 complete replacements | Minimum218 source DAG against K219's206; no table allocation or complete enumerator calibration |
| K220 global register permutations |40,320 permutations for each of original/copy-result/cache-result sources, with current-theorem register fixed |Identity is sole 220-state minimum for all three |
| K219 global register permutations |Same three 40,320-permutation sweeps |Identity is sole 219-state minimum for all three |
| K219 extended-entry permutations |All 362,880 register permutations with exploratory opposite-bit CI/CD entries |Identity is sole 219-state minimum; next successful count 222 |
| K219 clean equality variants |All 16 archived finite synthesis hits | Accepted hit 10 remains best 219; others 220 or 221 with extended entries |
| Exact equality cost 6 |20,285,479 constructions over the archived 14-atom library |No finite-signature hit |
| Equality with residual transfer to D |33,540,769 constructions over 16 atoms |19 finite hits; permitted partial replacements have at least 209 source nodes |
| Disequality tag 3 with odd-code halt | Literal equality-as-negated-disequality translation, 64 comparator/existence-row variants, and bounded reparses | Best direct source has 209 nodes and exploratory table count 224 |
| Signed disequality rows | 45 formula combinations, three grammar parses, two comparator orientations | Minimum 228 nodes in this representation |
| Disequality tag 1 / membership tag 3 | 5,832 tag-placement and association choices | Minimum 213 nodes, or 214 under the zero-run bound |
| Signed rows in the inherited atom skeleton | 180 layouts without forced row boundaries | Minimum 209 nodes; unchanged signed baseline best |
| Negative equality with old rho6 | All 6^8 fixed-shape parameter layouts | Minimum 209 twice; best exploratory tables224 states |
| Negative equality with dual B | Full translated existence row, R1/J3 meanings; all6^8 parameter layouts | Minimum 217 twice; best exploratory tables232 states |
| Parities inside pairing fields | Eight exact partitions, 288 selected layouts | Minimum 226 nodes overall;229 under the zero-run bound |
| Split seed bundle | Twenty corrected guarded cleanup layouts, 486 finite cases each | Minimum 210 nodes; best exploratory tables224 states |
| Existing semantic subtrees | 58 small closed nodes, 11 entry domains, 42–75 test vectors per domain | No completed matching signatures; seven exact disjoint-register commutations give no source below206 nodes |
| Negative equality plus inverse MP | Full/compact rho1, new/old comparator, fourteen command associations:56 layouts | Minimum219 DAG; best exploratory table234 states |
| Shifted even codec plus inverse MP | Ten implication builders, full/compact rho1, fourteen command associations:280 layouts | Minimum221 DAG; every layout has zero run10 and fails the inherited six-zero source bound; no accepted table count |


The prefix-code source layouts are bounded association searches, not every possible program for each codec. The exhaustive claims apply only to the explicitly listed finite spaces. Missing primitive entries and decoder-binding failures are compiler limitations, not lower bounds on Turing machines.

## Correctness points that matter

The formula-code transformation applies one recursive bijection jointly to formula fields and variable labels. In particular, a matrix code reused as a private variable label must be transformed too. Applying the new constructors only to formula positions would not establish native-calculus equivalence.

The 81 literal formula builders include the forward MP builder. The proof-list and stack unpairing routines do not secretly decode an implication's tag; a formula codec change must update the builder, but does not require an additional formula-division routine there.

K219 represents the source node `(CD 6,CC 2)` at two native states, 13 and 108. `recompile219.py` permits those already observed duplicate representations during its decoder check. It does not merge them. The optional `--extend-direct` entry synthesis in the permutation script is explicitly a count-screening hypothesis requiring runtime proof; the only minimum table is the unchanged identity, which does not use the synthesized entries.

The dual-B formalism has a narrower proved scope than the original negative-equality variant: membership must remain tag1 with F=R00, and the full translated existence row must remain. Compact existence and exchanged odd meanings are not justified by that proof. Apart from the two explicitly verified 219-state MP variants described below, the listed changed-source state counts are exploratory decoder counts, not machine certificates.

The split-bundle cleanup must pop at most once if both freshness comparisons fail. Its first pop must also clear the saved c in scratch7 before unpairing the formula stack. The bounded gate checks explicitly cover these two cases.

A failed equality may transfer residual scratch 6 into parameter D at MP, but a global replacement is unsound. At the first private-code gate, that parameter still holds `a` for the second freshness comparison. With `a=c=2,b=0`, the proposed transfer shifts D to 3 and can miss the forbidden original collision `a=c`. The retained exact first gate is essential in the measured partial replacements.

## Verified 219-state MP variants

The exact source and native tables are under `inputs/k219_no_push_copy/` and `inputs/k219_no_push_cache/`. Both remove the old MP command's dummy stack push. The first copies its conclusion to the current theorem, while the second moves it into the cache. Both passed `UNIVERSAL_MATHEMATICAL_PASS` in the full symbolic runtime checker and `CANONICAL_TABLE_AND_COMPLETE_BLANK_STARTUP_PASS` in the canonical replay. Each reaches logical registers `[3,0,0,0,3,0,0,0,0]` after 312,617 blank-tape steps; sparse and dense simulations agree.

| Variant | Source leaves | Symbolic cases | Symbolic steps | Native SHA-256 |
|---|---:|---:|---:|---|
| Copy conclusion | 4,725 | 6,142 | 1,511,178 | `530f9866566929681bdf783fe21ce044e0b81047c6bdd59df54cca70102296e8` |
| Cache conclusion | 4,721 | 6,137 | 1,510,372 | `ae0cc5d730cdb39da13e23eec725f48d96a0a254c1b9402521af30edfb8fc3e5` |

The four `receipts/verified_k219_*` summary files identify the exact inputs and results. The main delivery's `machine/` directories contain the complete case certificates and canonical tables. The earlier compiler receipts remain unchanged as records of the original count screen.

## Portable replay

Run these commands from the bundle directory with Python 3.10 or later:

```sh
python3 prefix_codecs.py
python3 row_permutations.py
python3 row_permutations.py --reverse-rho1
python3 inverse_mp.py
python3 pairing_mirror_assocs.py
python3 rebase219.py
python3 eq219_variants.py
python3 global_permute_int.py --source K219_Construction_2026-10-20/machine/sites219.json --table K219_Construction_2026-10-20/machine/k219.native.tm --name generated_registers219 --allow-old-duplicates --all-registers --extend-direct
c++ -O2 -std=c++17 closed_parse.cpp -o closed_parse
python3 disequality_codec219.py
python3 disequality_simple219.py
python3 disequality_signed219.py
python3 disequality_tags219.py
python3 disequality_signed_atoms219.py
python3 disequality_dual219.py
python3 disequality_row_permutations219.py
python3 disequality_row_permutations219.py --dual
python3 inner_parity_codec219.py
python3 split_bundle219.py
python3 split_bundle_corrected219.py
python3 source_facts219.py
python3 semantic_subtree219.py
python3 disequality_inverse219.py
python3 shifted_even_inverse219.py
python3 dyadic_pairing219.py
```

The complete 9! screen took approximately 293 seconds in the research environment and writes a large per-permutation summary. The supplied receipt keeps its exact aggregate histogram and the best records. Other scripts also write generated subdirectories next to their pinned inputs. The support module defaults to the bundle directory; `ENCODING_WORKSPACE` selects a different fully provisioned workspace, and `row_permutations.py` has an explicit `--workspace` option.

For the finite equality discovery search, compile the archived C++17 program and pass the included atom signatures. Its finite signatures and stopping rules are part of the declared search scope; finite synthesis is not an unbounded semantic certificate.

`sha256_manifest.json` identifies the included artifacts. The small bundle intentionally omits redundant copies of every generated source layout and the large finite-signature intermediate dictionaries; the scripts recreate them.

## Independent native-calculus audit

`theory_audit/` contains the independent positive-equality T/B countermodel audit, its exact native-AST checker, and the five pinned Rocq inputs. This negative theorem does not apply to the later negative-equality plus B system. Replay the syntax binding from that directory:

```sh
python3 audit_t_native.py --codes222 Codes222.v --codes230 Codes230.v --kcode230 KCode230.v --thm222 Thm222.v --enum222 Enum222.v --receipt replay.json
```

`receipts/portable_validation219.json` records a successful clean-copy replay of eight new experiment scripts with identical aggregate results apart from elapsed time. `receipts/portable_inverse_addendum.json` records a second clean-copy replay of the two final inverse-codec scripts, with exact aggregate receipt agreement. All included Python scripts passed compilation. `receipts/latex_validation219.json` records a standalone LaTeX build of both report sections; the parent report supplies the final PDF and layout review.
