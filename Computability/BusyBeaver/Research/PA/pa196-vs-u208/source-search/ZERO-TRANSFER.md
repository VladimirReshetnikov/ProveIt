# A reachable zero-transfer specialization of the PA196 source

The zero-input transfer-loop idea used in the incoming
[PA208 source optimization](../../../../../../docs/incoming/pa_consistency_research_2026-10-29.zip)
has an analogue in PA196. From the imported program's **clean source seed**,
a loop at old ordinals 3773–3775 can be removed while preserving source-level
halting. This is a source specialization: no 195-state table, physical tape
simulation, exported PA proof, or new PA-consistency equivalence follows.

The exact deterministic patch is to take the source trie node at binary path
`1010101110` and replace that one occurrence with its right child. The deleted
left child has three leaves, in old ordinal numbering:

| Site | Instruction | Successors |
| --- | --- | --- |
| 3773 | decrement register 1 | zero: 3776; positive: 3774 |
| 3774 | increment register 6 | 3775 |
| 3775 | `continueTo 2` | 3773 |

The zero branch is the original source's identity transition; the two other
sites are unreachable from the seed. The patch reduces the leaf count from
3,812 to 3,809. The count of distinct internal nodes **increases** from 159
to 160, because specializing a shared part of the trie creates distinct
ancestors. This explains why fewer source instructions alone do not show a
state saving in the binary machine.

## Finite invariant and source simulation

The imported
[`initial`](../../jamesyc-upstream/pa196/PA196/Source/Nonhalting.lean)
is `commandConfig 25 2 0 0 zeroStore`. The
[register layout](../../jamesyc-upstream/pa196/PA196/Source/CommandRegisters.lean)
and [zero store](../../jamesyc-upstream/pa196/PA196/Logic/CommandSoundness.lean)
give initial register vector `(2,0,0,0,0,0,0,0,0)`.
The upstream blank-tape connection is a separate dependency; this certificate
starts at the clean source seed and does not recheck the 58,154 tape steps.

Track register 1 as either zero or positive. Increment sets its category to
positive; its zero decrement takes only the zero edge, and its positive
decrement takes the positive edge with either output category. Instructions
on other registers preserve the category, and their decrement takes either
branch. The checker starts at `(site 25, zero)`, computes an inductively closed
overapproximation, and then checks initial inclusion and closure of all 6,275
location/category pairs independently. At 3773 the only category is zero; at
3774 and 3775 no category occurs. An induction on source steps proves the
corresponding property of every concrete run from the seed. The abstraction
also admits arbitrary values of all the other registers, so it does not rely
on sampling a blank-tape computation.

There is a concise local explanation: site 3760's zero exit reaches 3763
after clearing register 1; the subsequent 3763–3767 region does not modify
that register. The only other incoming edge to 3773 is the loop back from
3775. The abstract closure check handles the complete control graph, including
all other potential entries and the initial seed.

Let `f` preserve the order of all old ordinals other than 3773–3775, and
let `f(3773) = f(3776)`. The checker verifies every one of the 3,809 retained
instruction rows and successor edges under that projection. On a reachable
visit to 3773, the old machine takes the zero branch without changing any
register. Thus each new source step matches one old step, or one old step
followed by that zero-test step; conversely each old step is matched after
skipping that test. There cannot be an infinite run of skipped steps: its
zero successor is retained. Induction gives identical register values at
matched boundaries and preserves halting in both directions for the clean
seed. All source controls resolve within the trie; there is no normal root
exit requiring a separate cyclic-restart case.

The program is resolved twice, before and after the patch. One resolver uses
binary path successor and cut, mirroring the imported syntax; the other uses
ancestor intervals and ordinal successors. Their complete graphs agree. This
is an ordinary finite, checkable argument and a PA-formalizable simulation
outline; it is not itself a Lean proof or an exported PA derivation.

## Reproduction

From the repository root, using Python 3.10 or later:

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search/verify_zero_transfer.py --output /tmp/pa196-zero-transfer.json
```

The verifier checks the exact program hash and the three files determining the
seed, the independent resolvers, the register-1 closure, the three removed
ordinals, the deterministic path patch, all retained projected edges, and the
DAG/leaf counts. It writes the full semantic result to JSON; it matches
[`zero-transfer-receipt.json`](zero-transfer-receipt.json). It also computes
an independent zero/positive overapproximation for each individual register
from the same seed: within this abstraction, site 3773 is the only reachable
decrement that is forced to have zero input. This is not an exhaustive search
of stronger relational invariants or other source transformations.
