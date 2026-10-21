# Shared semantic lemmas

Two isolated kernel-checked refactors replace repeated reasoning while preserving every original declaration and executable definition. The combined endpoint check is recorded separately in [phase5 Lean evidence](../lean/README.md); this feature packet makes no claim about its outcome.

| Module | Shared argument | Lines | Bytes | Final isolated check |
| --- | --- | ---: | ---: | ---: |
| [ConstructibleAbs](../../../../../../../../Lean/BusyBeaver/ZFC/ConstructibleAbs.lean) | Bounded quantifiers transport between a constructible subtype and ambient members by transitivity | 997 → 992 | 52,100 → 52,054 | 3.371s, no warnings |
| [InternalSat](../../../../../../../../../../SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/InternalSat.lean) | Pair/numeral equality factors constructor-tag inversions; clause specifications compose existing equivalences | 1,433 → 1,321 | 66,837 → 60,730 | 2.877s, no warnings |

ConstructibleAbs adds two private transport lemmas and reuses them in four proofs. All 73 existing declarations and seven definitions remain unchanged. The quantified satisfaction argument still restricts the outer code witness before transporting the bounded object quantifier. Identical baseline/candidate clients pass, with five unchanged standard-axiom reports in each run. See the [complete diff](constructible/source.diff), [API comparison](constructible/api-comparison.json) and [independent source peer](peer/constructible/review.json).

InternalSat adds two private equality lemmas, removing 56 repeated impossible-tag branches from eight inversions. Two formula specifications then compose existing equivalences. The tag lemmas do not restrict potentially nonstandard payloads; the certificate-functionality proof is unchanged. All 79 existing headers and 30 definitions/structures remain unchanged, and the three axiom reports match the baseline. See the [complete diff](internal-sat/source-final.diff), [comparison](internal-sat/comparison-final.json), [source peer](peer/internal-sat/review.json) and [final comment-only successor acknowledgment](peer/internal-sat/final-review.json). ConstructibleReflect and NamedForm254 were inspected without changes.

`evidence.tar.gz` and [index.json](index.json) preserve all held text sources, source versions, comparison scripts, original runners, raw logs, records and peers. ConstructibleAbs failed inference attempts 1/3/4, earlier successful 2 and final 5 remain distinct. InternalSat failed 1, corrected 2 and comment-only final 3 are retained. Each final invocation used one worker, the shared proof lock, 120s and 12,288MiB caps. Historical `canonical_unchanged` fields refer to the isolated checks before integration. Original absolute scratch paths are retained; `paths.json` maps them to archive members. No object files or full predecessor cache are included.

Attribution: review_upstream_reflection authored the ConstructibleAbs refactor; drop_contract independently reviewed its proof delta. opening_encoder authored the InternalSat refactor; review_upstream_reflection reviewed its proof delta and final comment successor. The saved reader checks records and source/log bindings without running Lean or archived code:

```sh
python3 review_saved.py --output /tmp/k215-semantic-lemmas-review.json
```

It does not recreate the original kernel checks or independently verify live predecessor objects. The [result](result.json) records that bounded scope; the full current closure belongs to the separate combined evidence.
