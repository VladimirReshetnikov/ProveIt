# Physical search and quotient-MP source experiment

This is an additive research packet for the primary K215 at ProveIt commit
`53269bcab1efc0f82d3022645bd7cf0c22d84959`. **It contains no 214-state result.**
It contains exact source prototypes and bounded search evidence, with the scopes
below. The new semantic quotient-detachment theorem is supplied separately by
the enclosing research report.

## Results

| Construction | Source subtrees | Primitive occurrences | Physical count/status |
|---|---:|---:|---|
| Pinned primary K215 | 202 | 4,751 | Existing accepted 215 |
| Quotient source v00 | 211 | 4,751 | No accepted binary allocation |
| Quotient source v06 or v07 | 210 | 4,751 | Missing right-child decrement entry in inherited allocator |
| Polarity-compatible lowered v00 | 212 | 4,753 | Conservative price 234; prefix/entry check only |

All displayed source variants have maximum depth 47 and maximum zero run 6.
The mathematical arithmetic proof is in `quotient/quotient_macro_proof.md`.
It proves the replacement interface on all natural inputs. Two independent
complete-MP finite runs each cover 5,688 cases; those regressions corroborate
the proof and do not replace it. No binary universal runtime or blank-start
calibration was newly proved for any prototype in this packet.

The cost increase matters: the original source has no separate literal
constructor-tag test to delete. Its MP comparison already builds the tagged
implication and tests numerical equality. A semantically weaker rule therefore
does not automatically produce a shorter implementation.

## Bounded physical survey

The corpus is the primary machine and 20 integrated principal alternatives,
with exact table bytes and source paths in `inputs/variant_index.json`.
For each table we computed a radius-five local-tape reachability
overapproximation, starting from its declared start state on every binary tape.
The primary machine has 87,795 abstract contexts.

Two searches found no sufficient contraction in this finite grammar:

1. Identify two noninitial states, allowing both rows of the retained state to
   change, while implementing each old step by an exact whole-tape block of at
   most 31 transitions through otherwise unchanged provider states.
2. Identify two disjoint state pairs sharing one branch in each pair, replacing
   each differing branch by a neighbor-marker selector, and pay for both fusions
   with one synthesized selector. Existing provider transitions stay fixed.

Neither result is a lower bound or a statement that 214 states is impossible.
The abstraction can contain unrealizable contexts; bounded blocks can miss
longer simulations; initial states and other transformation grammars are
excluded. The three primary marker profiles reproduce existing 52/176,
124/127, and 160/190 constructions, which is a useful control rather than a
novelty claim. The new scope is the recorded cross-candidate survey; similar
baseline-only searches already occur in the repository's context-returns work.

## Reproduction

Python 3.10+ and the standard library suffice. Run without `-O`. Use fresh
output paths outside this packet; these commands need no network access.

```sh
python3 code/quotient_mp_source.py --source inputs/sites215.json \
  --vendor code/vendor --output /tmp/quotient-source-new
python3 code/lower_quotient_source.py --output /tmp/quotient-lowering-new
python3 code/check_quotient_mp.py quotient/sources/v00/sites.json \
  --output /tmp/quotient-full-mp-new.json
python3 code/check_quotient_mp.py quotient/sources/lowered_v00/sites.json \
  --output /tmp/quotient-lowered-mp-new.json
python3 code/price.py --seed inputs --source inputs/sites215.json \
  --output /tmp/quotient-price-identity-new --identity
python3 code/price.py --seed inputs \
  --source quotient/sources/lowered_v00/sites.json \
  --output /tmp/quotient-price-lowered-new
python3 code/survey_corpus.py --output /tmp/k215-provider-survey-new
python3 code/survey_corpus.py --shared-helper --output /tmp/k215-selector-survey-new
```

The full two survey commands may take several minutes. Saved summaries are in
`evidence/`; the full primary provider catalogue is retained there too. Saved
paths in the original receipts describe the construction environment and are
provenance fields only; portable commands use the included inputs.

## Attribution

The accepted machine, source syntax, `build221.py`, `source_splice.py`, and
conservative `price.py` are inherited from ProveIt. Their notices and terms are
under `licenses/`. The new local-window survey scripts, quotient source splice,
arithmetic argument, and finite complete-MP checker are additions prepared with
AI assistance for Vladimir Reshetnikov. They do not claim invention of the
underlying calculus, compiler, or existing marker transformations.

The exact rejected prototype is intentionally not advertised as a smaller
machine, and the 234-state prefix-only price is not an accepted consistency
machine. Its transition table is reproducible with the included allocator.
