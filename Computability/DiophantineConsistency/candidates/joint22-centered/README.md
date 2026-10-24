# Centered joint22: 22 integers, degree 14, 119 gates

This separate research candidate combines the joint-guards packet's
22-variable integer system with the centered-Pell packet's root shear.
It has **22 unrestricted integer unknowns**, exact degree **14**, and a
literal shared evaluator with **119 live binary arithmetic gates**.
Its polynomial has an integer zero exactly when the pinned joint22/16
parent does. All six fixed coefficient ports are preserved byte for byte.

The candidate improves the delivered centered22/14/123 evaluator by four
gates. Against joint22/16/118, it trades one gate for two degrees. These
are comparisons of explicit evaluators, not optimality claims.

The entire change is `y_old = y + f*o`. The old `y` occurs in only one
residual, and the parent evaluator already shares `f*o`. One extra addition
therefore computes the new polynomial. Cancellation in that residual lowers
its degree from eight to seven. `PROOF.md` gives the complete invertible
witness maps, all ten residuals, and the exact nonzero leading form.

`equation.json` specifies every residual as a polynomial in the declared
22 coordinates and six fixed numeral leaves. `circuit.json` gives every
binary gate, without unnamed operations or extra quantified registers.
`coefficients/BINDING.json` and the six retained gzip payloads give the
complete coherent `mixed-parity-unrounded-1064921` tuple, totaling 615883
uncompressed bytes. MF already contains its beta shift. The two determinant
scales are unchanged. This is not a new compact printed definition of those
constants, and does not license replacing them with the compact54 tuple.

Reproduce the finite checks using Python 3.12 or newer, with no dependencies:

```sh
python3 build.py --check
python3 -O build.py --check
```

Checks use a restricted arithmetic AST and exact sparse integer polynomial
arithmetic over the witness and coefficient symbols. They authenticate every
provenance file and compressed/raw coefficient payload, check the complete
forward and inverse row identities, expand each complete DAG residual, check
the sum-of-squares finalizer over independent row atoms, and verify the full
degree-fourteen homogeneous component. Both runs write their own receipts.
Acceptance does not rely on Python assertions, numerical samples, or a
syntactic degree estimate. Normal generation omits `--check`; it changes
only this candidate's generated packet and receipts.

No Lean command was run for this candidate, in accordance with the user's
pause. Its unconditional new conclusion is an ordinary integer-polynomial
isomorphism to the parent. The parent's unbounded native/Pell/refutation
calibration and the encoded object-ZFC derivation remain inherited
obligations; this finite certificate proves neither consistency nor
independent unsolvability.
