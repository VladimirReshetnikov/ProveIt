# Joint source, grammar, routing, and scanner exploration

**Result: no validated machine below 245 states was found in this packet.** The packet contains a new combined 245-state control, an exact-substring large-neighborhood optimizer, a scanner/grammar cost variant, bounded searches with expanded terminal-entry permissions, and their precise verification boundaries. A finite unsuccessful search is not a lower bound.

## The combined 245-state control

`control245/grammar.json` combines the inherited original-layout DNE mask32 source with the previously verified four-projection bootstrap relaxation. Its 128 transparent grammar states and 117 framework states produce a complete binary machine with canonical SHA-256:

```
6b3c24a9f1f3261246217ba90460701f7b30aa5c18d65901f9b36addea1d8dd3
```

The literal table is `control245/machine.tm`, starting in state 0, with working states 0–244 and separate halt label 245. The old-label table starts at 95, dispatches at 96, and halts at 254. The source has 6,366 leaves, maximum depth 49, and maximum zero run 6. The compiler independently checked all 8,269 guarded affine cases, a source bisimulation with 3,085 pairs and 6,168 edges, and the exact blank initialization in 407,995 transitions. Sparse and dense simulators agree on the head, state, and every one-cell. The resulting dirty root has logical registers `[3,0,0,0,3,0,0,0,0]`, header distance 181, and 167 spare blocks.

The independent whole-frame proof **passed** in 344.72 seconds; its full certificate is `control245/whole-frame.json`. It re-derives four block theorems, three arithmetic macros, and nine register selectors on the actual table, and treats all nine register values, extra header gap, and the nonempty spare suffix parametrically. The new control uses only inherited terminal orientations. Its source-to-calculus transfer is the inherited DNE mask32 theorem, retained as `inherited/logic-transfer.tex`; this packet does not claim a new Lean or Coq final endpoint.

## What the new search changes

`code/anneal_fine_lns.cpp` extends the inherited fine-token, routing-aware annealer with simultaneous deletion and repair of 1–4 nonmandatory dictionary words. It reparses every affected parent against live exact substrings, finds a short segmentation, then synthesizes a compatible binary tree through dynamic programming. Proposals preserve literal source words. Exact dictionary closure, all caller projections, scanner zero bound, and depth bound remain explicit checks. This crosses larger dictionary boundaries than the inherited one-node rotation or one-boundary resegmentation moves.

The experiments combine two inherited source shapes with 50 retained bootstrap projections, three progressively expanded terminal-entry families, and an additional zero-lock family. Every omitted projection and newly permitted orientation appears explicitly in the candidate metadata. The relaxed structural auditor checks those declarations; it does **not** infer an initialization or runtime theorem from them.

The 14-state permission family permits both incoming bits for these fine words and physical states:

| Fine word | Physical state | Original permitted bit |
|---|---:|---:|
| E | 110 | 0 |
| O | 122 | 1 |
| K | 125 | 1 |
| G | 127 | 0 |
| W | 146 | 1 |
| J | 149 | 1 |
| D | 17 | 0 |
| c | 204 | 1 |
| S | 36 | 0 |
| A | 39 | 0 |
| P | 67 | 0 |
| T | 72 | 1 |
| b | 77 | 0 |
| F | 93 | 0 |

The runtime investigation checked this family on binary outer prefixes of lengths 1–7, partitioned by final bit, within valid zero-6 contexts. The all-zero word of length 7 is excluded, and internal PCs producing seven consecutive zeros are explicitly skipped. Register data and all guard cases of the retained PCs are symbolic. That finite prefix scope is not a universal theorem over every possible outer prefix or every subsequent reassociation of atom interiors. A smaller resulting table would still need actual-table universal replay. The broad 21-permission experiment deliberately includes permissions subsequently found to fail in some contexts; it is preserved as a speculative proposal search, not a sound compiler interface class.

The six completed grammar runs made **28,707,797 proposals**, each retaining at least 128 grammar rules. The fully unlocked 14-permission final grammar uses three new orientations: state 77 on the right of `Ab`, state 67 on the right of `NP`, and state 127 on the right of `ZG`. Its actual 245-state table is **rejected**. Although source bisimulation passes, affine case `pc=001010` exhausts symbolic fuel. More decisively, the exact blank run reaches state 42 at head 5 after 51 steps, with one-cells `{-3,0,2,3}`. Its row `(42,0) → (1,R,42)` then repeats forever on the blank right ray. This is an exact induction argument for a bad bootstrap, not merely failure to find a frame within a time limit. The rejected table, affine error, and finite ray-trap certificate are retained under `rejected245/`.

`code/anneal_fine_joint_cost.cpp` additionally minimizes grammar count plus one extra scanner role when the maximum zero run is 6. A cost of 128 would propose either 127+117 or 128+116 working states. A small secondary potential rewards removal of distinct sixth-zero sites. The actual shorter scanner and blank initialization would still require independent verification. The runtime packet records the bounded run of this variant.

`code/milp_fine_relaxed.py` adds exact words from other search grammars and a bounded rotation closure to a finite-dictionary integer model. The two-round model contains 3,177 words and 26,574 productions; its 120-second HiGHS run produced no feasible 127-rule assignment. This was a time limit, not an infeasibility result. The three-round model reached 29,411 words and 1,239,167 variables, then its process was killed with exit 137. No solver result was obtained from it.

## Reproduction

The packet is self-contained for the supplied structural audits and literal control rebuild. Python 3 and a C++17 compiler suffice for those operations. Only the optional MILP needs NumPy and SciPy.

Run the quick independent structural audits:

```sh
python verify.py
```

Rebuild the literal 245-state control, replay all guarded affine cases, and reproduce its exact blank frame:

```sh
python verify.py --build-control --output replay
```

Run the more expensive independent whole-frame theorem:

```sh
python verify.py --whole-frame --output replay-frame
```

Repeat a bounded grammar search:

```sh
python verify.py --search masks14_unlock --seconds 60 --output search-replay
```

Use `--iterations N` together with a sufficiently large time allowance when comparing proposal counts. Time-bounded stochastic runs need not stop on identical proposals across machines. RNG seeds, elapsed times, proposal counts, constraints, resumes, raw outputs, restored source metadata, and structural audits are preserved under `experiments/`. `summary.json` is the machine-readable result ledger. The default audits do not upgrade any uncompiled search output into a physical machine theorem.

## Attribution and scope

The numerical calculus is attributed to Mira-Cult, the upstream verification to Jeff Ketchersid and contributors, and the compiler framework to Andrew James Wade. The 245-state foundation, DNE source transformation, Boolean row transformations, four-lock relaxation, and prior optimization families are inherited ProveIt work. New material here consists of the simultaneous dictionary repair extension, joint scanner objective, explicitly combined experiment families, finite rotation-closure model, the newly compiled combined control, and its fresh evidence. Original notices and licenses remain with the runtime sources.
