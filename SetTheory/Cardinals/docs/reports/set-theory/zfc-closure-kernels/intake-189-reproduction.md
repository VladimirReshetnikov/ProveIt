# Recovering and replaying batch 189

Run from the repository root with new output directories outside the repository:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover-intake189.py /tmp/intake189-recovered
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake189-fresh-state-search/prepare.py --packet /tmp/intake189-recovered/ZFC_218_State_Search_2026-10-20/ZFC_218_State_Search_2026-10-20 --output /tmp/state-search-direct
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake189-fresh-state-search/run.py --work /tmp/state-search-direct
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake189-literal-check.py --packet /tmp/intake189-recovered/ZFC_218_Research_2026-10-20/ZFC_218_Research_2026-10-20 --output /tmp/research218-literal.json
```

Recovery restores all 1,036 original files, including articles, supplements,
nested predecessor archives and original relative paths. It executes nothing.
The [placement map](data/intake189-placement.json) binds every retained member
or alias. Flattened archival scripts may still refer to their original paths;
use the recovered layout and the reviewed direct adapters above.

The five-job Source 145 plan checks the closed rho6 replacement, each complete
source/binding/canonicalization/startup, and each final generic runtime.
Small leaves have 60-second process caps; each full runtime has 240 seconds.
Assertions remain enabled. Final status is `FRESH_DIRECT_LEAVES_PASS`, not the
submitted wrapper's omnibus status. The [actual run](data/intake189-fresh-state-search/actual.json)
and [review](data/intake189-fresh-state-search/review.json) record all passes.
The portable preparation recovers the same selected inputs from nested ZIPs;
its normalized plan was checked against the executed adapter. Heavy runtimes
were run once. No manifest, ancestor verification, or proof assistant is run.

The final command is our narrow Source 146 audit: exact initialized-core patch,
complete 85-step failure trace and ray premises, plus the alternative219's
instruction-word identity and complete 312,617-step startup. It imports no
submitted executable module. It does not rederive that packet's full runtime,
validate its alternative source CFG, or reproduce its research searches.
The [record](data/intake189-literal-check.json) preserves those limits.

The [independent manuscript review](intake189-source-review.md) and
[intake reconciliation](intake-189.md) give the all-natural theorem arguments,
current-status corrections and open obligations. Exact-table Lean/PA status
is unchanged. The successful contextual218 arrival is batch 190 and is not
included in these commands.
