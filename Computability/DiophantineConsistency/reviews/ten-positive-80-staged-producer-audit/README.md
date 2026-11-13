# Seven staged 80 proof producers

The earlier selected-closure producer search did not match seven fresh
`Direct80*` objects because their guarded producers store multi-stage
`result.json` receipts, rather than the single-object `terminal.json` format.
`check.py` checks the successful stage, its object against the final selected
hash, retained source snapshot and stdout/stderr hashes, and every explicitly
pinned predecessor in each receipt. It also resolves each serialized direct
import on the recorded producer search path today and confirms its hash
matches the final selected closure. All seven passed; see
`observations/attempt01.json`, SHA-256
`276cd1faa3ebbcc59f149bb4104686c65982f187278aa44cb90a5c9c367373e6`.

Those receipts do not all individually pin every direct import: for example,
the product-power helper imports `ArithmeticPow` in addition to its explicitly
pinned predecessor. Current re-resolution is not evidence of unpinned bytes
at the original producer time. Full producer-time transitive source/object,
package and dynamic ancestry therefore remains open. This audit does not
assert anything about the 24 other fresh-header objects unmatched by the
earlier single-object receipt search. Rerunning the script requires the pinned
temporary providers and a new output path; it refuses to overwrite its result.
