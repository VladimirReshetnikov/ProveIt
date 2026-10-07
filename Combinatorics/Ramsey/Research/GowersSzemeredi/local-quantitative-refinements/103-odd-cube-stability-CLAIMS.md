# Claim ledger

All theorem numbers refer to `odd_order_cube_stability.pdf`.

## Main claims proved in the manuscript

1. **Theorem 3.3 — exact tail-energy identity.** The full fifth-through-eighth-order inclusion-exclusion tail is `-35 r E(f) - W(f)` with an explicitly defined nonnegative Bernstein remainder. Applies to every finite abelian group and every `[0,1]` function.
2. **Theorem 4.2 — complete complement decomposition.** The complement cube count equals the explicit polynomial plus twice the parity fourth moment, minus `(12h-35r)` times the energy defect, minus the remainder. No density restriction on the identity itself.
3. **Corollary 4.3 — sharp small-hole bound.** For vanishing parity moment and `0 < r < 12h/35`, the explicit polynomial is an upper bound, with full equality classification.
4. **Theorem 5.1 — optimal tail coefficient.** The universal coefficient 35 cannot be lowered, even for odd cyclic groups. Sharpness is asymptotic along sparse powers-of-ten sets.
5. **Theorem 6.1 — weighted subgroup-boundary estimate.** Extends the predecessor's set estimate with constant `2^(k+1)-2` to `[0,1]` exterior weights.
6. **Theorems 1.1 and 7.1 — exact local profile.** Resolves the predecessor's `conj:oddexact` for distance at most `1/50`; gives weighted and parity-corrected refinements, exterior penalty, and Boolean equality cases.
7. **Theorems 1.2 and 8.5 — weighted global rounding.** Deficit below `1/2000` gives a unique nearest coset within normalized distance `35 epsilon`. Odd order then gives the exact cubic profile.
8. **Section 9.1 — inverse profile.** Exact inverse bound and coefficients through order six, sharp along admissible odd subgroup indices; no claim that all real distances are attainable.
9. **Theorem 9.1 — near-equality rigidity.** Exterior mass is at most `2 gamma/(7 delta)`; under `gamma <= delta^3/1000`, normalized distance to a coset with one subcoset removed is at most `2 gamma/delta^2`.

## Credited antecedents, not claimed as new

- Qualitative subgroup/phase structure of near-extremizers in the broader Gowers literature.
- The predecessor's set subgroup-boundary constant.
- The exact torsion-sensitive coset-deletion formula.
- Elementary near-maximal-energy rounding; re-proved to make the weighted argument self-contained.

## Explicit limitations

- The finite verification scripts do not prove the general statements by themselves.
- No kernel-checked formalization or independent referee review is claimed.
- The density and global-rounding thresholds, exterior penalty constant, and rigidity constants are not claimed optimal.
- Only the tail-energy coefficient and the admissible-distance local equality profile have the specified sharpness proofs.
- The odd-order profile is false without a parity restriction; the article gives an even-order counterexample.
- No global Szemeredi improvement, Erdős-progression conclusion, or validation of the motivating OpenAI preprint is claimed.
- Historical priority of the new identities is provisional; the concrete advance over the predecessor's stated conjecture is explicitly documented.
