# Proposed nonnegative tau lift

The removed sign15 coordinate occurs only in its defining `tau` row and twice in retained `N0`. Set `q=beta*J+1`, `Y=s*q^3`, `E=(w*q)*Y`, and `k=eta+zeta`, with shifted natural coordinates positive. The signed replacement is `E*N+k−Rank`. An arbitrary reduced assignment can make this negative; the checker contains a negative example that is not asserted to be a seed zero.

The proposed noncircular route is to extract the unchanged retained Nt equation from a sign14 zero, assume represented ports, `beta>0`, `MC<beta` and `MF<2*beta`, and apply the existing model `scalar_window` theorem. It yields `Rank+2 < w*s*q^4 = E`, using neither the deleted tau witness nor N0. Positivity of shifted N and k then gives `Rank ≤ E*N+k`. The natural truncated subtraction `E*N+k−Rank` therefore embeds as the intended signed difference, giving the deleted coordinate. Each arithmetic inference, the sign14 Nt extraction and all cast/coordinate identifications remain to be Lean checked.

With this natural representative, transfer the five retained residuals and the removed tau row in both directions; then prove same-input existential equivalence under the explicit port bounds. This would still require the sign15 symbolic endpoint and a separately checked endpoint transport. It would not by itself bind the Lean expression to this external JSON or the 14-variable PDF.
