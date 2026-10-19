# Local runtime investigation below 246 states

**No complete machine below 246 states is certified here.** The 245-state
table is an experimental local transducer. Its zero operation rotates register
values and its header continuation differs from the inherited interpreter.

## The positive local result

Delete state 255 and change three rows of the pinned old-label Prefix246
table: `75/0 -> 1 R 131`, `112/1 -> 1 R 112`, and `131/0 -> 1 L 48`.
Positive decrement and increment keep their exact local arithmetic contracts.
For `B(v)=0 1^(v+1)`, zero decrement changes `B(A) 00 B(S)` to
`B([0] ++ A ++ S)` and returns to state112 at head−1, in
`4*sum(A)+4*len(A)+9` steps. The selected zero moves to the front.

`mtf-local.tex` gives the ordinary universal induction proof and the exact
five-step header obstruction. `verify_mtf.py` independently checks the literal
cycle premises, the whole-tape obstruction, and 2,040 local regression cases.
The changed row112/1 also acts after the local macro has returned; reaching
the old exit state therefore does not recover the old conditional protocol.

## Reproduction

Inputs are the parent archive's unchanged `zfc_prefix246_old.tm` and
`Prog254.v`. No duplicated baseline is included in this directory.

```sh
python verify_mtf.py --baseline /path/to/zfc_prefix246_old.tm
python mtf_cfg.py --program /path/to/Prog254.v
g++ -O3 -std=c++17 pulse6.cpp -o pulse6
./pulse6 /path/to/zfc_prefix246_old.tm narrow- 0 600
./pulse6 /path/to/zfc_prefix246_old.tm broad- 1 600
```

Run Python without `-O`; assertions are verification gates. The first command
rebuilds the experimental table and its verification JSON. The second
recomputes the prepared-source-root permutation diagnostic and independently
checks closure of both the product invariant and permutation relation.

The source CFG diagnostic closes at11,117 site/permutation pairs. It assumes
an initial source frame with `N,D >= 2` and the other seven logical values zero.
It canonicalizes names of registers known to be zero by the checked product
invariant. It does not assert that the experimental blank machine reaches such
a frame, repair the header continuation, or produce a specialized binary
decoder.

## Six-row bounded resynthesis

`pulse6.cpp` deletes255 and frees both rows of75,112,131 simultaneously.
All other rows remain literal baseline rows. Its48 fixtures include positive,
zero and increment cases, varied selected positions and unary values, and
value-one spare blocks. A goal must be reached at tick1 through249. The
baseline is an exact finite positive control under the same horizon.

The depth-first search intercepts an unassigned row before using it, branches
over every allowed action, and rejects a partial assignment only when its
literal execution already fails a fixture within the fixed horizon. Earlier
successful fixtures cannot depend on later-assigned rows. Consequently a
completed no-survivor run covers the entire finite assignment family, although
it does not prove semantic impossibility beyond the chosen horizon or goals.

| Family | Successor states allowed for an unknown row | Formal recipes | Lazy search nodes | Outcome |
|---|---|---:|---:|---|
| Narrow | `48,63,75,95,109,112,131,73,83` | `36^6 = 2,176,782,336` |17,450,713|Complete; no survivor|
| Broad | `2,4,6,7,10,14,20,28,31,38,40,44,48,56,60,63,64,69,73,75,83,95,109,112,131` |`100^6 = 1,000,000,000,000`|167,759,701|Complete; no survivor|

Each allowed successor has all four write/direction choices. All48 goals are
the inherited local contracts, including the unchanged-register zero goal.
These are finite recipe and execution bounds, not a working-state lower bound.
The `best.json` records reach only a15-fixture prefix, and are not solutions.
The local rotation theorem was developed from the best narrow record.

The bounded simulator stores cells−128 through383. Within the249-step
endpoint horizon and goal heads0 or−1, a returning successful run cannot leave
this window: reaching a cell below−128 and returning to either goal requires
more than249 moves; cells beyond383 are unreachable within the horizon.

## Exact source identity and attribution

Prefix246 old-label SHA-256:
`303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee`.

Literal register program SHA-256:
`1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746`.

The baseline and block notation come from the supplied ProveIt Prefix246
contribution, retaining its Mira-Cult/Jeff Ketchersid/Wade lineage and notices.
The source parser, counter normalization, and product transfer in `mtf_cfg.py`
follow the earlier `reachable_guards.py` contribution; the move-to-front
permutation specialization and independently checked closure are additions.
The finite search extends the prior pulse255 experiments from at most four
free rows to all six surviving rows of75/112/131 together.
