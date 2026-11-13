# Directional source reassociation screen

This screen applies the directional source reassociation criterion from
`analysis/directional_associativity.md` in the incoming
[PA208 research archive](../../../../../../docs/incoming/pa208_research_2026-10-29.zip)
to the source tree in the imported
[PA196 program](../../jamesyc-upstream/pa196/PA196/Program.lean). It looks for
reduced **source DAG** size, not a direct physical state deletion. The input
source SHA-256 is `8c7c6c6884ecbb8f56e893404bb81162db15ef3dd6fd3212881a93994d63d872`.

Run from the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search/scan_rotations.py --verify-graphs --output /tmp/pa196-rotations.json
```

The script resolves the exact input relative to its own location and uses only
Python's standard library. It checks the hash before parsing and verifies the declared trie root. Required checks raise explicit exceptions, including under `python3 -O`. It reconstructs
3,812 leaves and 159 distinct internal source nodes, agreeing with the upstream
program. [`receipt.json`](receipt.json) records the deterministic fields of
the run; elapsed time is intentionally omitted.

For subtrees `A`, `B`, `C`, a rotation between `((A,B),C)` and
`(A,(B,C))` is admitted when the escaping forward depth of `A` and the
escaping backward depth of `C` are zero. For a decrement the leaf depths are
`(1,0)`, for `breakTo k` they are `(k,0)`, for `continueTo k` they are
`(0,k)`, and for increments and halt they are `(0,0)`. Combining a left
subtree with depths `(f₀,b₀)` and a right subtree with `(f₁,b₁)` gives
`(max(f₀−1,0,f₁), max(b₀,b₁−1,0))`. These depths are the criterion used by
the referenced directional reassociation result; the middle subtree is not
required to be closed.

The script reports:

- Of the 1,037 allowed **single-occurrence** rotations, 51 retain 159 distinct
  internal nodes and the remaining 986 increase that count. None decreases it.
- Replacing **all occurrences** of one structurally equal subtree yields 161
  distinct allowed first rotations. Of these, 62 retain 159 nodes and 99
  increase to 160. The optional graph verification reconstructs the complete
  ordinal control graph and checks every one of these 161 variants against the
  original graph. An intentionally invalid root rotation changes the final
  jump target from site 0 to site 11, which serves as a negative control.
- From each of those 161 first variants, the script considers every eligible
  all-occurrences rotation of a structurally equal subtree. None of the
  resulting 26,083 ordered two-rotation pairs has fewer than 159 nodes.

The single-occurrence and global searches are different: a single occurrence
can leave other occurrences intact, while a global replacement rewrites each
occurrence of the selected equal subtree. Proper occurrences of the same
finite tree cannot contain one another, so the latter is a family of disjoint
local rotations. The two-step search covers **global replacements only**;
it does not exhaust two individual-occurrence rotations or mixed strategies.

The graph check tests source instructions and ordinal successors. It does not
build a new binary transition table, test that the physical decoder and
arithmetic engine can share states, prove an internal PA equivalence, or rule
out a useful sequence of three or more rotations. The count of 159 source
nodes is not the number of physical states. A larger source DAG might also
permit a smaller physical allocation. Negative results in these bounded
families are not a lower bound on state count.
