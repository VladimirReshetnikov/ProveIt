# Context-sensitive decoder allocation diagnostics

The smaller source trees do not directly give smaller machines. A conservative
allocator gives exact internal decoder-prefix bindings for one K/S+QS source
at **241 states** and one mixed-commutation source at **262 states**. Neither
table has a primitive-runtime or blank-startup proof, and these counts are not
optimality bounds. The accepted machine remains at 218 states.

The inputs are candidate000 from the [K/S+QS span search](../k218-quantifier-stability/source-span-dp/README.md)
(208 distinct source subtrees) and candidate000 from the widened
[mixed-commutation search](../k218-ks-mixed-commutation/source-pricing/README.md)
(209 subtrees). Exact input copies and their original paths/identities are in
[inputs](inputs/) and [publication.json](publication.json).

## Two causes of the previous allocation failures

The existing global-pool allocator could retire a state whose direct source
role disappeared even though a retained decoder still used it as a helper.
On the QS input, retained state69 at unchanged prefix `11010010011000` takes
the internal route `69 → 78 → 89 → 104` on its zero branch. State89 was
repurposed, so the attempted table instead follows new rows into arithmetic
state17 and changes a prefix bit. The [first localized trace](evidence/result.json)
and [attempted table](evidence/attempted-global.tm) retain this exact failure.
The direct-predecessor pool criterion does not account for such intermediate
helper uses; final prefix validation correctly rejects the table.

Protecting all 38 states used as intermediate steps of old retained-role
internal-prefix paths removes that failure. A second failure then exposes a
different issue: state76 is moved to prefix `110100100110011011`. Its existing
backward selector chooses a subtree represented by state183, rather than the
required child. Old state/subtree associations therefore cannot be reused
without checking their new prefix context. The [protected trace](evidence/result-protected.json)
and [helper witnesses](evidence/protected-result.json) document this second
rejection. The attempted 226- and 227-state tables are failed specimens.

## Conservative allocation with explicit context checks

The [allocator](context_allocate.py) preserves all old rows except the source
root84. It reuses an old subtree at a new prefix only after simulating every
internal decoder path in that subtree with the actual known prefix bits and
checking the old state/subtree relation. Otherwise it builds fresh rows,
sharing identical pairs of transitions. Syntactically unreachable states are
then removed, followed by a complete prefix check and a retained-row check.

| Input | Fresh states | Removed old states | Total states | Time |
| --- | ---: | ---: | ---: | ---: |
| K/S+QS candidate000 | 28 | 5 | 241 | 0.086 s |
| Mixed candidate000 | 49 | 5 | 262 | 0.075 s |

Both remove old states135,142,174,185,214. These conservative results leave
context-dependent leaf contracts and other possible state reuse unproved.
They do establish that the earlier allocation failures do not refute the
source transformations themselves. They also show why source-DAG count
alone is an insufficient machine-cost estimate.

The exact successful results and prefix-only tables are in
[QS evidence](evidence/qs-context000-v2/result.json) and
[mixed evidence](evidence/m-context000/result.json). An initial own diagnostic
mistakenly started fresh numbering at300, which collided with native301;
its [failed result](evidence/qs-context000/result.json) is retained. The
successful version starts strictly above the largest existing state. The
initial script version was not retained; it is not reconstructed as an
original execution artifact.

## Reproduction and scope

From the repository root, using a new output directory:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k218-context-allocation/context_allocate.py \
  --source Computability/BusyBeaver/Research/ZFC/k218-context-allocation/inputs/qs000.json \
  --output /tmp/k218-context-allocation-new
```

Use `inputs/mixed000.json` for the second input. The portable driver changes
only argument/library path setup from the retained executed source in
[history](history/); that portable variant was source-reviewed without
repeating the runs. The two diagnostic-localization scripts in history keep
their original scratch paths and are not advertised as portable entrypoints.
No separate process stdout/stderr files were captured.

This packet uses the existing K221 source/decoder utilities and the earlier
global allocator, with `opening_encoder`'s new source-search inputs. Root
authored the failure localization, helper protection diagnostic and
context-aware allocator. No new symbolic runtime, startup, proof-assistant
check, smaller machine, or general state lower bound is claimed.
