# Finite search results beyond uniform state folds

These experiments were run against the exact public253 table and, for the
last search, the verified one-row shortcut variant. They use conservative
finite windows and local whole-tape matching blocks. They found no complete
one-state deletion within the tested sufficient criteria. **These are finite
negative results, not state-count lower bounds and not semantic refutations
of every rejected candidate.**

The helper `upstream_audit_tm.py` is copied from the user's ProveIt repository:

- Commit `426592ce97e52d309bfb8f0132411556650b7ac1`.
- Path `Computability/BusyBeaver/Research/ZFC/audit_tm.py`.
- Source URL: <https://github.com/VladimirReshetnikov/ProveIt/blob/426592ce97e52d309bfb8f0132411556650b7ac1/Computability/BusyBeaver/Research/ZFC/audit_tm.py>.
- SHA-256 `40e55849aaa1f40c3ef70e0b23fb8b7b1fa3d0742cc0ea6006d27e84d931291f`.

The three experiment drivers are new additions to that helper. Each recorded
JSON includes the input table hash and exact driver hash. None needs network
access or third-party packages. Labels are public compact labels, rather than
the original254 labels used by several previous ProveIt searches.

## Families and measured results

| Experiment | Abstract pairs | Local attempts | Complete deletions |
| --- | ---: | ---: | ---: |
| Independent incoming-target redirects, public253 | 335,369 | 65,016 | 0 |
| Independent incoming-row rewrites, public253 | 335,369 | 260,064 | 0 |
| Independent incoming-row rewrites, after certified shortcut | 333,593 | 259,056 | 0 |

Every search uses radius6, so 13 cells are known, and permits at most64 local
steps. The abstract windows admit both values for each newly exposed outside
cell. They are not windows sampled from a finite concrete trace.

For each proposed deleted working state p, collect all incoming rows from
other working states. Each such row is allowed its **own** retained target,
rather than redirecting every entry to one global target. For a target
replacement q, the local old run starting in p is compared with the replacement
run starting in q after the unchanged incoming write/move. A match must have
the same retained state, relative head, and entire known window. Two halting
outcomes may match regardless of final tape/head, because the property is
halting. No local step may read outside the initial known window.

The incoming-row extension permits each entering row to choose its write bit
and move direction as well as its retained working-state target. For each
deleted p and entering edge it tries 2 times2 times252 =1,008 replacement
rows. Targets are retained **working** states; a direct terminal replacement
is outside this experiment's candidate family. In contrast to the target-only
version, the comparison begins before the entering row, so all writes and
moves are included in the matching check.

In both versions, a replacement prefix is stopped before it enters deleted p.
Thus it cannot silently execute a different incoming row whose edit has yet
to be chosen. This makes the separate per-edge decisions compose. An accepted
block can end at a retained state before another edited row; the next block
then starts there. The original and candidate both make positive progress:
even a zero-length suffix in the target-only version is preceded by the one
incoming transition. A removed initial state receives a separate blank-start
obligation in the target-only driver. No candidate in the incoming-row runs
passes all incoming-edge obligations; the driver deliberately raises an error
if an initial-state survivor would require an additional initial certificate.

Edges are examined in descending context-size order, and a proposed deleted
state is rejected as soon as an entering edge has no accepted replacement.
This is an exhaustive screening of that edge's local replacement choices,
which is sufficient to reject the independent-choice deletion family for p.
The public runs each checked258 entering-edge groups across253 possible
deleted states; five groups admit some replacement, and each state's first
unsatisfied group then rejects its complete deletion. The post-shortcut run
checked257 groups and has four such groups. The JSON retains the checked edge
groups and complete certificates for their accepted local replacements.

These results are outside the previously recorded uniform-fold and
symbol-wise-fusion families. They generalize the repository's prior
edge-specific old107 experiment, which fixed two options for one incoming
edge and changed only the target of the other. No novelty claim is made about
the general method of local peephole optimization.

A failure can arise from an abstract context that the actual machine never
reaches, a need for more than64 steps, a need to read farther than13 cells, or
the restriction against crossing another edited entry before matching. It
does not prove that the candidate has a different blank-tape halting value.
The counts above do not include all arbitrary252-state machines or arbitrary
simultaneous mutations of retained-state rows.

## Positive shortcut discovery

`row_shortcuts.py` searches for a single replacement transition matching a
positive old block, with complete head/tape/control equality, over every
abstractly reachable input window of the edited row. The public253 radius6
run has exactly one nontrivial accepted row:

```text
60/read0 := write0, moveR, target51
```

No working state becomes graph-unreachable. This is the shortcut independently
certified in the parent folder by a much smaller radius2 invariant. The
recorded `shortcut-results-r6.json` is discovery data; the smaller certificate
and whole-run proof supply the main positive deliverable.

## Reproduce

From this directory:

```sh
python edge_redirect_search.py ../source_zfc253.tm --radius 6 --bound 64 --output /tmp/edge-results-r6.json
python incoming_row_search.py ../source_zfc253.tm --radius 6 --bound 64 --output /tmp/incoming-results-r6.json
python row_shortcuts.py ../source_zfc253.tm --radius 6 --bound 64 --output /tmp/shortcut-results-r6.json
python incoming_row_search.py ../zfc253_shortcut.tm --radius 6 --bound 64 --output /tmp/shortcut-incoming-results-r6.json
```

On the recorded environment these commands took approximately3.90,4.20,0.36,
and3.99seconds respectively. Times are engineering observations, not bounds.
The searches add no new consistency calibration and do not rebuild any
upstream Coq proof.
