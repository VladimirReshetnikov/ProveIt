# Reassociating the zero-transfer specialization

The directional reassociation search can also start with the source obtained
by the [zero-transfer specialization](ZERO-TRANSFER.md). Its 3,809 leaves
have 160 distinct internal nodes, one more than the original PA196 tree. The
verifier [`scan_pruned_rotations.py`](scan_pruned_rotations.py) first reruns the
zero-transfer certificate and requires its result to match the pinned receipt;
it then reconstructs the patched source in memory. It does not edit either
upstream snapshot.

Using the same closure criterion as the [original-tree scan](README.md):

- None of the 1,036 admissible single-*occurrence* rotations reduces the
  source DAG below 160 nodes.
- The 163 admissible all-occurrences rotations produce 61 variants with 160
  nodes and 102 with 161. The script compares the entire ordinal control graph
  of each variant with the pruned source. It also checks the invalid-root
  negative control: the last jump target changes from 0 to 11.
- From each distinct first global variant with at most 161 nodes, the search
  tests every second eligible global rotation. All 26,731 ordered pairs have at
  least 160 nodes: 3,828 yield 160, 12,453 yield 161, and 10,450 yield 162.
  No variant drops to 159 or below, so no second-step improvement needed a CFG
  check. The 163 first-step checks and negative control pass.

Run from the repository root with Python 3.10 or later:

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search/scan_pruned_rotations.py --output /tmp/pa196-pruned-rotations.json
```

The run takes about ten seconds in the original environment. Its deterministic
fields are in [pruned-rotations-receipt.json](pruned-rotations-receipt.json);
elapsed time varies. The two-step screen covers global replacements of
structurally equal nodes and does not cover two occurrence-specific or mixed
rotations, nor any three-step search. It does not allocate physical tape
states. A larger source DAG could still admit a better physical layout; this
negative result is not a lower bound on the state count or on the length of a
valid PA-consistency proof.

## Both cleanups

The same script can first apply both the zero-transfer and
[second cleanup](SECOND-CLEANUP.md) patches:

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search/scan_pruned_rotations.py --both-cleanups --output /tmp/pa196-double-pruned-rotations.json
```

It reruns and compares both checked source-specialization certificates
before reconstructing the 3,807-leaf, 162-node source. Among its 1,035
admissible single-occurrence rotations none reduces the DAG count. Its 163
admissible global single rotations have 162 nodes (61) or 163 nodes (102);
the script compares all 163 complete ordinal graphs against the two-patch
source. The invalid root rotation changes the last jump target from 0 to 9.
Of 26,731 ordered two-global-rotation pairs with the first intermediate at
most 163 nodes, 3,828 have 162 nodes, 12,453 have 163 and 10,450 have 164.
No improvement below 162 occurred, so no second-step improvement needed an
additional CFG comparison. Deterministic results are in
[double-pruned-rotations-receipt.json](double-pruned-rotations-receipt.json).
The single-occurrence, two-global, and bounded-search limitations above apply
equally to this run; neither source variant has a new binary allocation.
