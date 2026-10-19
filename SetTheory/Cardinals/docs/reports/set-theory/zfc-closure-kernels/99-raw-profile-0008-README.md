# Contextual state-18 addendum

**Bounded result: 128 grammar rules; no sub-245-state machine found.** This addendum is separate from the frozen main grammar packet.

The new search uses the fourteen proposed terminal permissions, 50 bootstrap locks, and an additional **contextual** interface for the fine terminal `C` (physical state 18). `C` retains its ordinary right-entry mask. It may occur directly as a left child only when the containing word is itself entered on bit 1, giving the safe suffix `10`. The companion runtime addendum supplies the local physical microtrace argument for this conditional contract.

## Recursive word masks

Masks 1 and 2 mean incoming bit 0 and incoming bit 1 respectively. For a production `w = a b`:

1. If `a` is the direct terminal `C`, the available incoming mask of `w` is restricted to 2.
2. Otherwise `a` must admit incoming bit 0; if it does not, the production has mask 0.
3. The right child `b` must admit incoming bit 1; if it does not, the production has mask 0.
4. If neither restriction applies, `w` admits both bits.

The optimizer recursively computes these masks after each candidate's dependency closure. Every mandatory root and every route root must admit both incoming bits; every charged word must have a nonzero mask. This is conservative for roots with a more specific known entry context. It prevents an apparently valid `C`-left word from being reused on an unsafe left edge.

The runtime investigator independently reviewed `derived_mask` and `context_ok` and confirmed these acceptance checks under the stated contracts. One inherited proposal generator still rejects direct `C` on the left during known-split resegmentation. That limits exploration, while rotations and simultaneous repair can propose the contextual use. It does not weaken acceptance checks.

`audit_contextual18.py` independently reconstructs masks and mandatory physical entry roots, tests boundary examples, and applies the inherited structural invariants with the contextual obligation already discharged. It reports `PASS_CONTEXTUAL_STRUCTURAL_ONLY`; this status is not an actual-table or blank-initialization theorem. The underlying fourteen permissions retain their separate composition obligations.

## Exact run

The 180-second run used RNG seed **181402** and made **1,848,127 proposals**, with 707,975 accepted moves, 3,817 uphill moves, 34 restarts, and 7 closure rejections. The best result has **128 rules**, leading-zero count 3, maximum zero run 6, and depth 46. The final grammar has no right-entry-only words and no direct `C`-left production. Its independent contextual structural audit passes. No literal-machine validation was performed for this final 128-rule search output.

The required source limits the opportunity: of the fourteen core required words, only `BDC` contains `C`, and the retained locks fix `BDC = B·DC` and `DC = D·C`. None of the twenty-two caller-projection target words contains `C`. Therefore the new direct `C`-left freedom cannot appear in these required words while these locks remain; any benefit in this search would have to arise through unconstrained selector padding. This observation concerns this explicit search family, not unrestricted encodings or source rewrites.

## Reproduce

Compile and run the standalone optimizer:

```sh
c++ -O3 -std=c++17 anneal_fine_contextual18.cpp -o contextual-search
./contextual-search grammar.txt constraints.txt repeat.json 180 181402 127 lock50.txt resume.txt
```

Independently audit the frozen final candidate, using the runtime supplied in the main grammar packet:

```sh
python -B audit_contextual18.py candidate.json --runtime /path/to/main-grammar-packet/runtime --output repeat-audit.json
```

Time-bounded runs can stop on different proposals on other hardware. The exact final output and run log are included. No unrestricted lower bound or new proof-assistant endpoint is claimed.
