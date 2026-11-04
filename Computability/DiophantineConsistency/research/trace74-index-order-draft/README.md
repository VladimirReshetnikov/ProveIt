# Guard-free ordering of first and odd Pell indices

`graph_first_lt_odd` proves `n < r` from the two stated ordinate identities and
positive coordinates. `graph_ordered_indices` supplies both indices for the
same positive trace74 graph zero, retaining the oddness of `r` and the first
index residue. It does not identify the indices or establish a rank sign,
window, guard, or endpoint.

Author attempt02 passed, outer session 16246 exit 0. Its terminal SHA-256 is
`1babb66c4fec1944f29a762189d559e2d5fe4975f26f2acc94e890b0944135ac`.
The [independent result audit](../../reviews/trace74-index-order-result-independent/README.md)
passed. Attempt01 failed and is retained; its
reconstructed source and runner are labeled as reconstructions and match the
original pinned hashes. The direct-provider, search-path and full ancestry
limitations of the runner remain.
