# Adaptive bootstrap search beyond three edits

**Result: no whole-source-frame startup hit and no accepted sub-194 machine.** These new bounded experiments extend the inherited pair/triple screens to adaptive combinations of four through sixteen row edits. The growth-prioritized experiment completed thirteen depths and part of the fourteenth before its wall budget; its requested depth twenty was not completed.

## Inputs and provenance

The pinned repository is `VladimirReshetnikov/ProveIt@8d31445d858761a8f6150c2e5012adae8895e932`. In the paths below, `PA` abbreviates `Computability/BusyBeaver/Research/PA`.

- `runtime193.native.tm` is the unchanged table from `PA/docs/pa_sub194_research_2026-11-13/runtime193/`.
- `neutral.tsv`, `startup_any_frame_templates.tsv`, and `ax11_runtime193.native.tm` are unchanged inputs from `PA/docs/pa194_ax11_research_2026-11-14/research/startup_repair/`.
- `positive_primary.native.tm` is reconstructed using the primary PA194 packet's exact dense/native label map.

Input and source SHA-256 values are in `summary.json`. The corrected inherited pool has 327 edits; it excludes nine `35/0` edits invalidated by the corrected source-envelope analysis. Pool members were individually screened in a restricted runtime context. **Simultaneous source preservation of arbitrary combinations is not assumed.**

## Method and acceptance condition

A candidate consists of an initial control and a sorted list of nonconflicting row edits. After a literal blank simulation, the next generation adds an edit only to a row actually encountered in that trace. No row receives two edits. A reproducible beam retains frame-proximity elites and diverse terminal or bounded behaviors. The growth variant additionally favors transiently richer tape.

A hit requires the entire finite-support source frame at native control 84: its unique left marker, an exact path for one of source sites 25–44, a zero gap of at least 48 cells, all nine encoded primary registers, a nonempty encoded spare list, and blank exterior. Both source grammars' path arrays were checked (`template_binding.json`). The criterion allows arbitrary primary values. A hit would still require a sound source-seed argument and fresh universal runtime checks before it could be accepted as a consistency machine.

Runs stop at the stated step limit, the inherited approximately 24,900-cell displacement window, more than 20,000 one cells, literal halt 254, or a directly recognized outward blank self-loop ray. A resource-bound stop does not prove divergence.

## Results

| Source / initial controls | Beam | Step limit | Completed edit depth | Candidate runs | Literal transitions | Hits |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Runtime193 / all 193 | 512 | 50,000 | 12 | 97,664 | 4,128,677,587 | 0 |
| Runtime193 / control 74 | 1,024 | 100,000 | 16 | 325,606 | 29,888,561,386 | 0 |
| AX11 runtime193 / all 193 | 512 | 100,000 | 12 | 96,154 | 8,112,605,779 | 0 |
| Runtime193 / control 74, growth priority | 1,024 | 100,000 | 13, then 16,069 runs at depth 14 | 248,499 | 22,975,007,878 | 0 |

The totals are 767,923 runs and 65,104,852,630 transitions; 709,278 runs use at least four edits. These count execution work, **not disjoint machines**: experiments overlap, and earlier edits can become inactive. There were 2,085 literal halts, 71,962 recognized rays, and 693,876 resource-bound stops. The bound stops remain unresolved beyond their cutoffs. The older pair/triple searches are not included. No state-count lower bound, or exhaustive obstruction for this edit pool, follows.

## Relevant controls

The original primary PA194 positive control reaches its exact complete source-site-25 frame after 58,154 transitions, with head coordinate -2, gap 0, physical registers `[0,0,0,0,0,0,2,0,0]`, and 26 one-valued spares. Its complete support appears in `positive_control.jsonl`. The unchanged Runtime193 baselines reproduce the historical two literal halts and 191 outward rays across all 193 initial controls. These checks exercise the simulator and whole-frame detector. They do not prove source preservation for edited tables.

## Reproduce

Use a C++17 compiler. The all-start original-core run used `-O0`; the others used `-O2`. Seeds, counters by depth, and compiler version are recorded. The wall budget makes the last cutoff hardware dependent; increase that argument to finish a fixed depth.

```sh
g++ -std=c++17 -O2 adaptive_startup.cpp -o /tmp/pa-bootstrap
/tmp/pa-bootstrap runtime193.native.tm neutral.tsv startup_any_frame_templates.tsv 12 512 50000 300 -1 5082193 > replay-all.jsonl 2> replay-all.log
/tmp/pa-bootstrap runtime193.native.tm neutral.tsv startup_any_frame_templates.tsv 16 1024 100000 300 74 74193 > replay-74.jsonl 2> replay-74.log
/tmp/pa-bootstrap ax11_runtime193.native.tm neutral.tsv startup_any_frame_templates.tsv 12 512 100000 300 -1 11193 > replay-ax11.jsonl 2> replay-ax11.log

g++ -std=c++17 -O2 adaptive_startup_growth.cpp -o /tmp/pa-bootstrap-growth
/tmp/pa-bootstrap-growth runtime193.native.tm neutral.tsv startup_any_frame_templates.tsv 20 1024 100000 180 74 742193 > replay-growth.jsonl 2> replay-growth.log
```

Arguments are `table edits templates max_depth beam_width step_bound wall_seconds start seed`; `start=-1` selects every working control. These are optional discovery searches, not required gates for checking a delivered 194-state fallback.
