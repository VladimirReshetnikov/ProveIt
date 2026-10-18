# Carry-tail reductions: proved partial statements and bounded searches

**No complete machine below 246 states is certified by these experiments.**
All labels below are the old labels of the supplied context246 table.
Its exact SHA-256 is
`303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee`.

## The proved 245-state partial result

Delete state 255 and change only `75/0` from `1 R255` to `0 L112`.
The resulting table has 245 working states and 490 transitions.
Write `B(v)=0 1^(v+1)` and `width(A)=sum(v+2 for v in A)`.

For any finite prefix A, arbitrary left and right exteriors, and a valid
following block, both decrement macros retain their exact original output:

- A positive selected value `x+1` becomes `x`, with exit state 48 at the old
  origin, the extra boundary1, and duration `2*width(A)+4`.
- A zero selected value remains zero, with exit state 112 at head -1,
  no boundary shift, and duration `2*width(A)+5` (two steps shorter).

The ordinary symbolic-induction proofs use the audited context246 block
rules, not finite testing. They inspect neither opaque exterior. These are
not new proof-assistant kernel theorems.

Increment fails on the smallest local input: selected0 and one spare0.
Start state 73, head 0, with ones exactly at `{-1,3}`. The inherited contract
requires state 48, head -1 and ones `{-1,1,2,4,6,7}` at step15. Instead the
partial table reaches state 131, head -3, ones `{-2,0,1,3,5}` at step15;
its first return to 48 is at step16, head -4. The complete trace is supplied.

From the delivery root, reproduce these artifacts with:

```sh
python3 experiments/tail/verify_decrement245.py
```

Outputs are `decrement245_partial.tm`,
`decrement245-proof-and-counterexample.json`, and
`decrement245-increment-counterexample.tsv`. The script supports `--base`
and `--output-dir`; source-tree use and delivery-tree use both work.

## State255 deletion search

`search_pairs.cpp` uses 15 local fixtures, a2,000-step bound, a2,304-cell
tape array, and forbids movement left of the macro interface at -1.
Every row choice ranges over two writes, two directions and 245 retained
targets:980 actions. The unmodified baseline passes all fixtures first.

| Family | Assignments | Smallest zero passes | Also smallest increment |
|---|---:|---:|---:|
| Vary109/0 and 75/0 | 960,400 | 981 | 0 |
| Vary75/1 and 75/0 | 960,400 | 983 | 0 |
| Four109/0 actions targeting 75; both75 rows arbitrary | 3,841,600 | 2,947 | 0 |

All three families were run under both spare contracts. The strict contract
preserves all old blocks except the selected increment, allowing any finite
valid appended spare list, including empty. The loose contract permits the
old final spare to be replaced by any finite nonempty valid spare list.
Neither version had a complete survivor.

The three-row enumeration has an explicit reduction:109/0 is the only
original incoming edge to 75. If its target changes,75 is unreachable from
these macro entries; changing the two75 rows cannot rescue a path already
rejected by the 109/0 two-row family.

Four triples passed all 10 decrement samples with 83/0 unchanged. Sweeping
980 choices of 83/0 for each gave 3,920 further trials and no smallest
increment survivor. This is not an exhaustive arbitrary four-row search.
The exact four cores and run counts are in `search-results.json`.

Commands from the delivery root:

```sh
c++ -O3 -std=c++17 experiments/tail/search_pairs.cpp -o /tmp/zfc-tail-pairs
/tmp/zfc-tail-pairs baseline/context246/machine/zfc_prefix246_old.tm 10975 /tmp/pair10975.json
/tmp/zfc-tail-pairs baseline/context246/machine/zfc_prefix246_old.tm 75both /tmp/pair75both.json loose
/tmp/zfc-tail-pairs baseline/context246/machine/zfc_prefix246_old.tm triple /tmp/triple.json loose
/tmp/zfc-tail-pairs baseline/context246/machine/zfc_prefix246_old.tm inc83 /tmp/inc83.json loose
```

## A retained-mark and return-flag search

Fix `75/0=0R255`, `255/1=1L63`, `48/0=0L112`, `112/0=1R10`,
delete 131, and vary255/0 and 112/1 over 980 actions each.
`search_zero_flag.cpp` screens90 whole-instruction fixtures, with a5,000-step
bound and at most15 wrong dispatcher returns. All baseline fixtures pass.

Of960,400 assignments, five pass the first increment and positive-decrement
fixtures under the exact target convention; none also passes zero decrement.
The five `(255/0,112/1)` pairs are:

```text
(1L63,  1R75)
(1L75,  1R75)
(1L109, 1R75)
(1R48,  1L255)
(1R63,  1R75)
```

Allowing any valid nonempty spare suffix and either the original header or
a header shifted right by one gives1,987 first-two-fixture passes; all fail
the third fixture. These searches are bounded rejection results, not
impossibility theorems.

```sh
python3 experiments/tail/prepare_zero_flag_cases.py
c++ -O3 -std=c++17 experiments/tail/search_zero_flag.cpp -o /tmp/zfc-zero-flag
/tmp/zfc-zero-flag baseline/context246/machine/zfc_prefix246_old.tm experiments/tail/zero-flag-cases.txt /tmp/zero-flag-strict.json strict
/tmp/zfc-zero-flag baseline/context246/machine/zfc_prefix246_old.tm experiments/tail/zero-flag-cases.txt /tmp/zero-flag-loose.json
```

A proposed state 48 marker also relied on an invalid context assumption.
The ordinary baseline CI fixture at path0111, logical register 0, all
primaries0, spare[0], span40 reaches state 48 reading0 with a left-neighbor1
at literal step362. Thus that neighbor alone does not distinguish an
exceptional zero-return mark from an ordinary program-counter carry.

The additional `search_branch83.cpp` fixes `75/0=0L112`, `48/0=1L131`,
`131/0=0R7`, deletes255, and sweeps all 980 choices for 83/0. Under the loose
spare contract all 980 pass the smallest zero macro and none passes the
smallest increment. This uses the same bounded local simulator; it does not
resolve or assume away the state 48 context obstruction.

```sh
c++ -O3 -std=c++17 experiments/tail/search_branch83.cpp -o /tmp/zfc-branch83
/tmp/zfc-branch83 baseline/context246/machine/zfc_prefix246_old.tm /tmp/branch83.json loose
```

## Detector-entry audit

`audit_detector_entry.py` adds assertions to the inherited affine executor
and replays all 8,391 arbitrary-parameter instruction cases. It checks 191,434
state 6 entries, with the right cells fixed to `+1=0,+2=1`. Each entry has
either its first leftward1 at distance 0 through 7, or nine known zeros at
positions -8 through 0. There are21,316 long entries and 36 distance-seven
entries. Oracle-internal detector transitions use only protected6/1, which
is the distance-zero case.

The extra ninth zero is necessary for the old continuation: its last row
is `74/0=0L84`. A one at -8 could otherwise make the baseline restart at -7,
while the new eight-state model restarts at 3. The verified recurrent entry
guard closes this exact proof obligation. Blank startup is a separate finite
check. This result is stronger than a finite-value trace census and remains
an ordinary symbolic-frame proof, not a new kernel endpoint.

```sh
python3 experiments/tail/audit_detector_entry.py
```

The script supports `--base`, `--output`, and the `ZFC246_BASE` environment
variable. It finds the sibling `experiments/decoder` directory in the
delivery and the original `analysis/decoder_reduction` directory in the
research workspace.

## What remains useful to try

The 245 partial table needs a phase-sensitive increment closure using its
retained states. The 244 forward-carry result in the sibling experiment has
one state of budget available, but must preserve its branch bit before the
proved exact configuration collision. A downstream repair with a single
designated return event, such as the first later dispatcher entry, cannot
return different successor PCs from that same configuration. This does not
exclude a common future run visiting two target frames at different times;
the bare existential-segment simulation relation needs a separate argument
if that possibility is allowed. A strengthened
spare-count or control-phase invariant would have to exclude one member of
the collision and be proved initially and after every instruction. Merely
restricting all spare values to 1 does not exclude that collision.

The separate seven-state detector synthesis remains attractive because
its inputs admit finitely many exact local contracts; an independently
replayed model would still need integration and a fresh blank bootstrap.
