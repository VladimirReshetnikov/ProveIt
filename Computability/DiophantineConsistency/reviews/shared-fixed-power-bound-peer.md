# Independent ordinary review of the fixed power bound

The root reviewer read the complete candidate proof and the pinned
`Pell.eq_pow_of_pell` forward construction as inert source, without
editing or running Lean. Its choice `max n k` is used only through
positivity and the two upper-bound inequalities. Replacing it with any
`W>=n,k` preserves the construction:

* `A=chi_(W+1)(W)` exceeds `n^k`, and the standard Pell congruence
  makes `psi_(W+1)(W)` divisible by `W`.
* The positive modulus `T=2An-n²-1` exceeds `n^k`; reducing the
  conjugate Pell expansion gives the required power congruence.
* The indexed-Pell criterion supplies the remaining witnesses for the
  actual index `k`, with the same signed-quotient encoding.

Thus `W=n+k` supplies fresh witnesses for every positive input pair.
Soundness restores the deleted natural bounds with `wn=k,wk=n` and
applies the unchanged original criterion. The last norm and retained
`A>=2` row force `Z!=0`, hence `A>W>=n`, before replacing the natural
subtraction in the power theorem by the ordinary signed congruence.
No unknown power output is used to justify that replacement.

Topological reconstruction preserves every later macro input, and the
parent's actual static positivity audit covers all55 emitted calls.
No equality between an arbitrary old certificate's free W and the new
fixed value is asserted. The change preserves existence by choosing new
Pell witnesses. The beta-majorant and integer companions are separate
artifacts; they are not silently modified here.

Root also replayed the complete deterministic generator in check mode
and the independent candidate checker. Both passed: whole squared-row
expansion,24-coordinate/15-constraint symbolic identity, affine
restoration, source pins, arbitrary-bound controls and55 distinct
base/exponent pairs. The bundled normal/optimized receipts preserve
the broader replay evidence. These finite checks supplement the
unbounded proof above; they neither prove consistency nor supply a new
Lean or internal object-ZFC derivation. The inherited C222/refutation
calibration remains explicit.
