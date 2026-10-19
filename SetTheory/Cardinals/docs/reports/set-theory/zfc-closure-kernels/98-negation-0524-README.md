# Orientation promotion and selective negation contraction

These are finite grammar-discovery experiments, with an independently written
audit of their retained outputs. No literal machine is claimed for these
unsuccessful families.

## Pay for an orientation-unrestricted implementation

The inherited dictionary has 14 composite terminal words that are restricted
to one branch orientation. `prepare_shadows.py` promotes one such word at a
time: it removes its zero-cost terminal status and gives it an ordinary paid
binary definition. The existing physical runtime is still fully charged.
This does not offer both a free and a paid implementation at each call site.

All 14 inputs start at 129 grammar rules, one above the baseline. Each received
20 seconds of the inherited dynamic grammar search, with seeds 8800 through
8813, target127, all54 bootstrap equations, and maximum zero run6. Across
**4,991,231** proposals, every retained output still has129 rules.

`summary.json` contains the complete trial census. `independent-audit.json`
contains the separately recomputed word, orientation, route, bootstrap, and
source-path checks. The searcher's inherited `framework_states:118` metadata
is not a newly measured state count; only the grammar counts are reported here.

From the packet root, a representative replay is:

```sh
g++ -O3 -std=c++17 dependencies/anneal_canonical_dynamic.cpp -o /tmp/zfc-direct-anneal
python3 -B work/terminal_shadow/prepare_shadows.py \
  --inputs dependencies/canonical_inputs --output /tmp/zfc-shadow-seeds
/tmp/zfc-direct-anneal \
  /tmp/zfc-shadow-seeds/shadow-000/grammar.txt \
  dependencies/canonical_inputs/canonical-constraints.txt \
  /tmp/zfc-shadow-seeds/shadow-000/candidate.json \
  20 8800 127 dependencies/canonical_inputs/canonical-lock54.txt \
  /tmp/zfc-shadow-seeds/shadow-000/resume.txt 6
```

The corresponding independent audit is:

```sh
python3 -B work/terminal_shadow/audit_grammar_input.py \
  --grammar /tmp/zfc-shadow-seeds/shadow-000/grammar.txt \
  --constraints dependencies/canonical_inputs/canonical-constraints.txt \
  --locks dependencies/canonical_inputs/canonical-lock54.txt \
  --candidate /tmp/zfc-shadow-seeds/shadow-000/candidate.json \
  --output /tmp/zfc-shadow-seeds/shadow-000/audit.json
```

The other trials use the analogous directory and seed. Elapsed-time searches
need not reproduce the exact proposal count on another machine; the retained
candidate can always be checked directly by the independent auditor.

## Selective negation contraction

`partial_negation.py` generates130 distinct subsets of the30 original negation
occurrences: none, all, singletons, complements, prefixes/suffixes, and groups
with matching nearby contexts. Every edit is the exact nine-to-four word
replacement proved in the accompanying theory section.

All130 were seeded. The unchanged control has128 rules; the smallest changed
seeds have131. The eight best nontrivial seeds received30 seconds each with
seeds11000 through11007 and the same54-equation/six-zero constraints. Their
**3,470,995** proposals left the outputs at131 or132 rules. The complete
seed census and the independent audits are retained. The 121 unscreened noncontrol seeds
are omitted as regenerable intermediate data, while all130 source variants
remain in `partial-negation-variants.json`.

Regenerate the full variant list and its seeds from the packet root:

```sh
python3 -B work/terminal_shadow/partial_negation.py \
  work/grammar/direct_negation_variants.json /tmp/zfc-partial-variants.json
python3 -B dependencies/grammar_search/seed_dne_variants.py \
  dependencies/fine_grammar /tmp/zfc-partial-variants.json \
  dependencies/fine_grammar/fine20261018.json \
  /tmp/zfc-partial-seeds --generic-edit
```

`partial-search-summary.json` gives the eight selected masks and counts.
Their search uses each seed's own grammar, constraints and resume file, with
`dependencies/fine_grammar/fine-lock54.txt`. The independent checker accepts
the same explicit paths. `work/theory/audit_source_variants.py` separately
checks the source semantics and clean-scratch premises for every supplied
partial contraction, including the unscreened variants.

## Scope and provenance

The source token identity is a semantic theorem at a proved register boundary.
The grammar auditor here checks exact binary word equations and supplied
finite routing constraints. A successful grammar would still require literal
table emission, unbounded runtime simulation and complete blank initialization.
None of these negative searches establishes a global state lower bound.

The dynamic annealer and input seed are inherited unchanged from the attributed
incoming research; their exact source origins appear in
`dependencies/archive-byte-audit.json`. The promotion generator, subset
generator, and independent finite-input auditor were written for this packet.
