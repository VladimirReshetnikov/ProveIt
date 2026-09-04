import FabiusFunction.StirlingFirstReverse

/-!
# The factorial row sum of the complete Bell polynomial

The source's list of Bell-polynomial specializations contains

`B_n(0!, 1!, …, (n-1)!) = n!`   (`bell_complete_factorial_pred`),

which was the one entry of that list the corpus did not carry.  It is the row sum of the
identity `B_{n,k}(0!, 1!, …) = c(n,k)` already in the corpus, and the row sums of the unsigned
first-kind triangle are already known to be factorials, so the proof is the composition of
three existing results and introduces nothing new.

Recording it as a named theorem rather than leaving it to the reader is the point: it is the
statement the source displays, and a crosswalk that pointed at the two halves separately would
be asking the reader to perform the last step.

## Main results

* `bell_complete_factorial_pred`.
-/

set_option autoImplicit false

namespace Fabius

/-- **The factorial row sum:** `B_n(0!, 1!, …, (n-1)!) = n!`. -/
theorem bell_complete_factorial_pred (n : ℕ) :
    Bell.complete (fun j => (j - 1).factorial) n = n.factorial := by
  rw [bell_complete_eq_sum_partialBell,
    Finset.sum_congr rfl fun k _ => partialBell_factorial_pred n k]
  exact sum_stirlingFirst_eq_factorial n

end Fabius
