# PA194 AX source-token binding

`PA194AXSource.lean` defines the 190-token decomposition of the actual AX
subtree `PA194.SourceTree.x67`. The kernel checks the count and proves that
the ordered primitive leaves of this subtree equal those obtained by
expanding the listed token trees. The last three tokens are the guard-copy,
guard-comparison, and closing transfer; the other 187 are computational.

This is a syntactic leaf-order identity. It does not by itself prove that
source control flow follows the tokens in sequence, that the macros realize
their intended operations, that the guard is correct, or that AX preserves a
PA-proof invariant. In particular, no internal PRA/iPRA theorem follows from
this finite identity alone. The source tree is the pinned Python translation
of the archive grammar described in `../pa194-source-tree/README.md`.

From the repository root, run:

```sh
Computability/BusyBeaver/Research/PA/pa194-ax-source/check.sh
```

The script reconstructs the source tree from the pinned upstream and archive
inputs and kernel-checks the two theorems in a fresh temporary directory.
