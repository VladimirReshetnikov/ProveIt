# Eighteen-clause raw-profile consistency kernels

This contribution gives an ordinary mathematical construction of finite universal clause theories equiconsistent with ZFC. It does **not** give a binary Turing machine with a new state count.

The new interpretation quotients only data values and membership, and evaluates formulas with raw assignment and class terms. Consequently, its equality predicate needs only left Euclideanity, membership transport, and a distinct-constants clause. **Every function-congruence clause and every incidence-congruence clause can be omitted.** Three selector coordinates suffice to construct relative power objects, whose iterates have strictly increasing predecessor sets; this supplies arbitrarily many distinct selectors without evaluation congruence. The complete proof, including the required inherited raw-EPSC calibration and the ZFC model expansion, is in `raw_profiles.tex`.

## Exact results

| Variant | Clauses | Proper functions | Fixed-opcode bits | Huffman bits | Selective-dictionary bits |
|---|---:|---:|---:|---:|---:|
| RP18D | 18 | 10 | 902 | 798 | 790 |
| RP18Z | 18 | 9 | 910 | 796 | **787** |
| RP18V | 18 | 9 | 906 | 795 | 788 |
| RP19ED | 19 | 10 | 1069 | 972 | 956 |
| RP19EZ | 19 | 9 | 1077 | 971 | 953 |

All variants have two constants, four binary predicates, and at most four local variable slots. RP18Z fuses the member selector with the counterexample function under complementary guards. The RP19E variants add one native coded extensionality clause. The intermediate RP19D/RP19Z and RP20ED/RP20EZ controls retained evaluation congruence; they remain reproducible and have their original exact payloads retained.

RP18V replaces the member selector by `V(x,d)`. Its upper construction uses a model of ZFC + V=L and definable assignment records containing their designated `d`-coordinate value as a literal member. This additional model construction and the ordinary constructibility consistency transport are proved or identified explicitly in the manuscript. It improves the nine-function flat and plain Huffman costs; RP18Z still has the smallest measured selective-dictionary stream.

The code-length headers, dictionary-count headers, dictionary definitions, all clause and literal framing, and final terminators are included in the compressed bit counts. Function signatures/arities belong to the specified decoder protocol. No decoder program, refuter program, blank-start initialization, or Turing-machine state cost is included in those static data counts. The exhaustive dictionary result is only over the declared finite sets of repeated subterms with the specified variable normalization.

## Reproduce

Python 3, standard library only, from this directory:

```sh
python raw_profiles.py --output results
python raw_profiles.py --output scratch-stage --stage 1
python raw_profiles.py --output control19_results --evaluation-transport
python encoding_experiments.py --output encoding_results
```

The first command checks all five exact template round trips, 2048 total ground-code round trips for each variant, and actual stage-zero CNF satisfying valuations. The second checks the RP18D stage-one CNF (177 clauses, 154 atoms, SAT). The third reproduces the previous theory with evaluation transport. The fourth performs independent prefix-code decode checks, including every one of the 1024 raw-theory and 8192 extensional-theory dictionary candidates per variant. Successful finite checks establish those implementation properties; they do not establish the mathematical consistency theorem or consistency of ZFC.

`results/` contains fully expanded clause JSON, fixed-width `.bits` streams, packed `.bin` files, and exact metrics. `control19_results/` retains the intermediate theories. `encoding_results/` contains `.huffman.bits` and `.shared.bits` streams plus dictionaries and exact charging records. `reference/` retains the original source44 full mathematical note, modules, and repository license. The reference modules are reused for source controls and the exact finite DPLL refuter.

## Proof and provenance status

The consistency equivalences are ordinary mathematical theorems internalizable in ZFC, with the inherited full raw-EPSC and extensional EPSC calibrations identified in the manuscript. They are not serialized Lean or Rocq proofs and do not claim a represented PA endpoint. The ideal unbounded ground-instance loop is specified and proved correct mathematically; no unbounded physical guarantee is claimed for the reference Python process.

The current ProveIt source checkout has commit `fd1adfa19f8fe8da41444e3fa43b89a59d891067`. The comparison against the earlier twenty-clause quotient reconstruction comes from `docs/incoming/zfc-sub245-research-20261018.zip`, whose report records source pin `6446ff5668307a2ac6aee1896037f0b792090389`. Primary references and the exact initial tape and entry restrictions of the Neary--Woods 15-state, 2-symbol universal machine are provided in the manuscript bibliography.

The raw 902-bit stream would occupy 11,872 cells under a literal bit-as-two-bi-tag-symbols mapping to that UTM, before its encoded program and control markers. This is a cost of that mapping, not a lower bound on all possible initializers or a reason a compact compiler cannot succeed. A concrete binary refuter and blank-start initializer remain to be constructed and counted.

The manuscript also proves that deleting the distinct-constants clause is unsound for this purpose: setting `d=q` gives a model on hereditarily finite sets, constructible in ZFC, in which the nominal binary profile becomes unary. Thus the resulting seventeen-clause theory has consistency provable in ZFC. The finite graph probe files enumerate all 16 two-point and 512 three-point membership graphs as an exploratory diagnostic; the general power-object proof is the actual justification for the eighteen-clause result.

For incorporation, retain this README, `raw_profiles.py`, `encoding_experiments.py`, the TeX manuscript, `results/`, `control19_results/`, `encoding_results/`, and `reference/`. The finite quotient probe and its two JSON outputs are optional research artifacts. Research extraction directories and Python cache files are not required.
