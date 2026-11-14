# Bounded two-cell history-fold screens

The recorded literal-table screens found no fold in the following explicitly
restricted family:

| Table | Zero-history controls | One-history controls | Pairs | Trace limit | Hits |
|---|---:|---:|---:|---:|---:|
| Incoming PA1944L | 54 | 52 | 2,808 | 21 | 0 |
| New PA194AX11G | 49 | 55 | 2,695 | 21 | 0 |

A candidate pair must have all incoming transitions move right and write the
corresponding history bit into the cell left of the current head. The merged
row can initially write either bit and move left to any existing helper control.
If the two original actions are already equal, that action is also admitted.
Subsequent proof steps follow unchanged literal transitions within the two-cell
window, cannot read exterior cells, and cannot use either merged control as an
intermediate helper. Each trace must reproduce the old one-step result exactly
(up to the proposed alias), including both local cells, head position and target
control. Controls 0 and 74 are conservatively excluded from the candidate pair
because they are possible dense/native start labels.

The screen considers all initial tape bits and both histories, so any discovered
fold would carry finite all-tape identities for this family. An empty result
excludes only these candidates at this trace limit; it does not exclude other
folds, larger windows, coupled changes, or a smaller machine.

`4L.native.tm` is the unchanged native table from the pinned incoming 4L archive;
`PROVENANCE.json` gives its archive member and SHA256. The AX11G input is the
package's `../../machine/machine.native.tm`. The two JSON receipts preserve the
completed original screens, with input paths made package-relative and SHA256
fields added. The script's algorithm is unchanged; its parser now comes from
`../../comparison/graph_tools.py`.

Optional full replays, from the extracted package root:

```sh
python3 -B research/two_cell/search_context_folds.py research/two_cell/4L.native.tm --bound 21 --receipt /tmp/4L-two-cell.json
python3 -B research/two_cell/search_context_folds.py machine/machine.native.tm --bound 21 --receipt /tmp/AX11G-two-cell.json
```

The two new receipts should agree with `4L.receipt.json` and `AX11G.receipt.json`
respectively. These finite search receipts are separate from the universal
source-contract verification of the delivered AX11G construction.
