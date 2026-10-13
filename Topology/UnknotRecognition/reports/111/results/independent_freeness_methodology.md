# Independent freeness review

The portable audit is `tools/audit_freeness.py`. It takes an explicit directory
containing the integrated `fastunknot` package, an optional JSON target, and an
output filename. It has no implicit dependency on a checkout location. Python
and the `regina` Python module are required; the saved run used Python 3.12.14
and Regina 7.4. Run without `-O`, because this audit uses assertions.

From the unpacked research package, reproduce the saved report with:

```bash
python tools/audit_freeness.py \
  --fast-root /path/to/ProveIt/Topology/UnknotRecognition/fast \
  --target certificates/figure_eight.json \
  --output results/independent_freeness.json
```

`--target` accepts either a compiled `source-disk-cut-presentation-v1` object
or a packet containing that presentation under its certificate. When saved
group proofs are present, the audit replays them as well as generating fresh
proofs. Omitting the target skips its component cases; the remaining corpus
contains 10,201 presentations. A fixed seed, 20261012, controls the random cases
and independent-oracle sampling. The report records hashes of the two audited
production modules and the target packet.

## Corpus and results

| Check | Saved-run count |
|---|---:|
| Presentations examined | 10,203 |
| COMPLETE presentations checked by explicit Tietze maps | 6,748 |
| INCONCLUSIVE presentations | 3,455 |
| Nonabelian S3 homomorphism-count comparisons | 481 |
| Separate Regina recognitions | 485 |
| Rejected certificate mutations | 3,240 |
| Saved figure-eight group certificates replayed | 2 |

The corpus includes all 1,365 two-generator, one-relator presentations through
word length five and all 7,225 pairs of two-generator relators through length
three. It also includes 1,600 cases with sparse generator labels and random
signed words, four known nonfree presentations, two known free presentations on
which the policy is inconclusive, five empty/trivial edge cases, and the two
figure-eight target components. No algebraic soundness defect was found.

## What is independent

The audit's word oracle repeatedly deletes adjacent inverse letters. It does
not import either production reduction implementation. It verifies the
conjugating words that witness cyclic reduction and derives every singleton
substitution directly from the equation `p x^epsilon q = 1`.

For each COMPLETE result it tracks the image of every original generator in
the final free group, verifies every original relator becomes the identity,
and checks the final surviving generators map identically. At each step it
also checks the legal defining relation for the eliminated generator. These
checks validate the Tietze isomorphisms, rather than merely checking the rank
of the abelianization.

Sampled presentations are evaluated against every assignment of their
generators to the nonabelian group S3. A free group of rank r has exactly 6^r
such homomorphisms. Separate Regina simplification and recognition supply a
second algorithmic comparison. These are additional checks, not substitutes
for the exact Tietze argument. Certificate mutations exercise source digests,
strict field inventories, pivot validity, boolean/integer separation, final
rank and generator lists, empty-relator inventories, and incomplete traces.

## Independence limits and policy limitations

This is a finite correctness audit. The audit and the production code use the
same signed-generator convention and the same mathematical Tietze criterion,
although their word-reduction implementations differ. The audit does not
independently authenticate a topological source, prove that its compiled
presentation is its fundamental group, or realize a group move as an embedded
handle move. Those obligations belong to the source compiler and the source
certificate verifiers. There is no timing or speedup claim in this report.

The policy is provably incomplete: the automorphism `a -> ab, b -> a`, applied
four times to the standard trivial presentation, gives
`<a,b | abaababa, abaab>`. Both relators have no singleton letter, so the policy
returns INCONCLUSIVE even though the group is trivial. An unused generator
gives an analogous free rank-one example. Both examples are included, and
Regina recognizes their groups independently.

The accepted total word length never exceeds its initial cyclically reduced
value. Trial substitutions can temporarily use quadratic space in that value;
the saved report's `peak_accepted_length` is a bound on accepted states, not a
measurement of peak memory.
