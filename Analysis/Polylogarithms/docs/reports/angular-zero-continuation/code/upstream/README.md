# Pinned upstream implementation

These two files are byte-for-byte copies from Vladimir Reshetnikov's ProveIt repository at commit
`9bc738d3be22b8586a24693f19fb2e2a50ecd1bf`. Their basenames were shortened for the original imports; their contents are unchanged.

Repository: https://github.com/VladimirReshetnikov/ProveIt

| Packaged file | Original repository path | SHA-256 |
|---|---|---|
| `full_ds.py` | `Analysis/Polylogarithms/docs/reports/gaussian-parity-reductions/code/18-signed-kernels-full_ds.py` | `c800e2c354b130e6ff6db1d5728ba0fba313ffa571d1e69848982b3224d2a9f7` |
| `gaussian.py` | `Analysis/Polylogarithms/docs/reports/gaussian-parity-reductions/code/18-signed-kernels-gaussian.py` | `d35247d63b24c922d3195325091eeb2424318d0523f8465b2e0fc47302cace4c` |

`full_ds.py` specifies the precise level-four, fixed-weight, depth-two product matrix discussed in the article. `gaussian.py` supplies its symbolic depth-one expressions and contains earlier exact interval routines. The new rank and normal-form verifiers import these files to compare against the pinned implementation. No claim that this finite matrix includes every polylogarithm relation is made.
