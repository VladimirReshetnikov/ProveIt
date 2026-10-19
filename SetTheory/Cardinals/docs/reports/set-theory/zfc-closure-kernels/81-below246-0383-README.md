# Macro redesign investigation

No machine with fewer than 246 states was found by this investigation.

## Certified runtime modifications

`neutral_macros.tex` is an integration-ready report section. Its strongest
result is the single-row replacement `131 0 1 R 103` (`gap103.tm`), which
preserves the entire existing spare suffix on increment. The original table
appends one `011` spare block on every increment. The replacement therefore
saves exactly three tape cells per logical increment, measured at corresponding
instruction boundaries from matched valid frames. It preserves all primary
updates and program-counter behavior. Its state count remains 246.

Two other replacements `75 1 1 R 73` and `75 1 1 L 73`, separately or combined
with the first, also preserve the recurrent register semantics while changing
spare production. Exact arbitrary-length macro contracts, their durations,
and the proof boundary are in the TeX section.

The five neutral macro variants in this section have not been supplied
with admitted blank initializers.
The spare-preserving variant and its combination with `75 1 1 R 73` had no
successful existing-state blank starts in the recorded bounded search.

## Proof checks

These reuse the frozen 246-state package's symbolic proof engine and pinned
source program. Pass that package's root as the optional first argument:

```sh
python3 -B check_neutral_macros.py /path/to/zfc-context246
python3 -B check_neutral_sites.py /path/to/zfc-context246
```

`check_neutral_macros.py` proves the four block traversal lemmas, three full
arithmetic macro contracts, and all nine marking contracts for each variant.
Its proof rules are the existing literal transition, unary self-loop induction,
finite block-list induction, and concatenation identities. It does not infer
universal behavior from bounded data.

`check_neutral_sites.py` reruns the source parser and affine symbolic checker
on all 8,391 guarded instruction cases for each variant. The new macro proofs
supply the altered suffix contracts; the abstract box records the same primary
effect and physical header shift. The suffix stays nonempty in every case.

The recorded output files are `neutral_macro_proofs.json` and
`neutral_site_proofs.json`. These are mathematical proof checks, not new
Lean/Rocq kernel endpoints and not blank-start consistency equivalences.

## Source-compiled runtimes and separate blank certificates

Two separately compiled tables now have both complete universal runtime
checks and independently certified blank prefixes:

| Exact table | Working states | Universal guarded cases | Transitions to the exact safe root |
|---|---:|---:|---:|
| `agent_states/colored_context_candidate_003.tm` | 246 | 8,391 | 410,735 |
| `agent_macros/compiled24_scanner250.tm` | 250 | 8,391 | 407,983 |

The independent `agent_states/check_blank_prefix.py` certifies these
prefixes in `agent_states/blank_prefix_results.json`. Each starts in state
95 with head zero on the all-zero tape and reaches state 96, head -5,
marker -6, header 176, and an empty PC. The physical primary vector is
`[0,0,0,3,0,0,3,0,0]`, followed by 167 spare blocks of value one. The check
compares the complete target tape, with exactly 351 one-cells and zero
everywhere else; the head stays inside the explicit checked window.

The runtime certificates retain their original, narrower scope. In
particular, `blank_initialization_proved: false` in a runtime-only audit
means that its checker does not perform initialization verification.
The separate blank-prefix certificate supplies that proof for the two
tables listed above. It does not apply to the five neutral macro variants
or to either rejected 245-state scanner table.

From the archive root, replay the blank certificates with:

```sh
python3 agent_states/check_blank_prefix.py \
  --reference sources/context246/zfc-context246/machine/zfc_prefix246_old.tm \
  --table agent_states/colored_context_candidate_003.tm \
  --table agent_macros/compiled24_scanner250.tm \
  --output /tmp/blank_prefix_results.json
```

`colored_runtime_summary.json`, `compiled24_summary.json`, and their TeX
sections distinguish the runtime and initialization certificates. Neither
table meets the requested strict bound of fewer than 246 working states.

## Discovery searches

The C++ searches require only a C++17 compiler and standard library.
The parent investigation's literal or semantic cases files supply finite
counterexample filters. All sampled searches are bounded and do not prove
minimality. None of the compiled executables is needed to use the proof checks.

- `search_boundary.py`, `search_two.cpp`, and `synthesize_core.cpp` searched
  local carry-tail circuits. The last searches modifications of `75/0` and
  `109/0` under four known positive-return rows, deleting state 255; no local
  positive/zero/increment contract survived.
- `combine.cpp` simultaneously retargeted all incoming edges to states 48
  and 2 using every individually surviving edge replacement. All eight and
  2,448 respective combinations failed the sampled instruction contracts.
- `neutral_mixed.cpp` recomputes row visits on each certified runtime variant
  before testing mixed-row state identifications with flexible valid frames.
  The five complete runs tested 597,334 recipes and had zero survivors.
- `neutral_edge.cpp` similarly recomputes visits before uniform merges or
  single-edge retargeting. No reduction emerged from any variant.
- `seed_search` was built from the frozen package's existing search source.
  The `*_boot_search.txt` files record bounded start-state searches and no
  admitted root for the two tested spare-preserving variants.

Machine filenames retain original labels, start label 95, and halt label 254.
For the five neutral macro variants, the start marker is a serialization
convention and does not assert successful blank initialization. The two
source-compiled tables listed above have separate complete blank certificates.
