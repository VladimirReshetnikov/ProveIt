# Independent factual audit: beta-only cover warning

Attempt01 is policy-rejected and excluded. The author reports actual outer session 96124 exited 1 and was reaped. Child result SHA-256 `1587a6ae3dc8466736f8382e6ec330217fda44a044bc120be7c481be62bc744b` records Lean exit 0 and null monitor reason, but stdout includes an exponent-8807 threshold warning and a `[propext]` report; strict runner rejects the warning. Outer terminal SHA-256 `7ff4d6e6aa1fe575a86b195308bee9579eb80954282cdcea33f85e57518568cd` records child exit 1/FAILED, with stable input/wrapper hashes. Independently verified stage and outer log hashes. No Lean replay was run.

The warning states exponentiation was not evaluated; it does not identify a timeout or invalidate previously checked component theorems. This attempt does not provide an accepted beta-bound cover theorem, actual mask cover, graph guard or iPRA result.
