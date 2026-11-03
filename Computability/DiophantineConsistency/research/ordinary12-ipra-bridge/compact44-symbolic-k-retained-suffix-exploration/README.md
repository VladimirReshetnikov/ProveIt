# Symbolic K byte gaps and suffix

This is an **author-only natural-number exploration** using the existing
symbolic-K and byte-window provider. The three sources compile without warnings
and do not expand the large integer. They do not prove a model theorem,
identify `paramKernel rho` with `kernelNat`, prove equality to a filesystem
file or gzip stream, bind the displayed tuple, or establish an iPRA theorem.

* `TopDigitClean.lean` proves the top base-`2^67` digit is 1, all digits with
  indices `5496 ≤ i < 8849` are zero, and
  `2^592883 ≤ paramKernel rho < 2^592884`. It uses the actual finite term
  positions; it does not need to evaluate the 943 row weights.
* `LastByte.lean` derives that symbolic bytes `46029` through `74109` are
  zero, byte `74110` is 8, and all later bytes are zero. The theorem
  `symbolic_suffix_literal` identifies every byte at offsets beginning at
  `46029` with the explicit zero-padded function that is 8 at offset 28081
  and zero elsewhere. This is a Lean equality to that function, not a Lean
  semantics for any external file.
* `MiddleGap.lean` uses the permitted copy and selector positions to prove
  the other symbolic byte interval `18442 ≤ j < 27613` is zero. Its
  coefficient-gap proof accounts for both reflected bands and every term,
  including the special copy anchors.

Together the two disjoint intervals and the final byte cover 37,253 positions
of the 74,111-byte retained payload. The Python
`check_retained_intervals.py` independently reads the pinned gzip, checks the
compressed and decompressed SHA-256 values and length, and checks these same
zero intervals and terminal byte. Its normal run exited 0, and `python3 -O`
was rejected with exit 1. This check is external; it supplies no Lean theorem
about file bytes, decompression, or the unexamined byte positions. In
particular it does not turn the suffix theorem into a formal binding of the
entire retained coefficient.

## Compiles and scope

The final sources were compiled sequentially in `/tmp/compact44-k-top-digit-explore`
using Lean 4.32.0, `-M3000 -j1 -DElab.async=false`, a 120-second timeout, and
`LEAN_PATH` consisting of that directory's `lib` followed by the existing
`/tmp/ipra-byte-k-specialization-01/lib`, `/tmp/ipra-sparse-k-family-01/lib`,
`/tmp/compact44-k-radix-cert-01/lib`, and Foundation package overlay. Terminal
sessions 39605 (`TopDigitClean`), 1126 (`LastByte`), and 36607 (`MiddleGap`)
exited 0; their compiler outputs are retained in `observations`. The middle
module was rebuilt after the final, warning-free `LastByte` compile. The
selected `#print axioms` reports include `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx`.

An earlier combined top-digit attempt exhausted kernel memory when it tried
to specialize a penultimate quotient; its source is retained, but its
tool-delivered output was not saved as a separate log. The two first
`LastByte` versions failed and are retained with their actual compiler logs;
the third compiled with an exponent-threshold warning and was replaced by a
general power-monotonicity lemma in the final warning-free source. Failed
`sorryAx` reports are not evidence. The provider and object hashes are
point-in-time post-run observations, not a paired replay or authenticated
fresh transitive closure; package and earlier provider ancestry is inherited.
