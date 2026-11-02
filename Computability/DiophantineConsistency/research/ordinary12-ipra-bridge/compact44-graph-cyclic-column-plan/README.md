# Proposed graph-to-cyclic-column interface (source-only)

This is an uncompiled interface, not an existing theorem. It uses the new symbolic `directK := paramKernel rho`; that expression is not yet bound to the retained bytes or displayed coefficient. The exact graph theorem must be joined over one coherent provider, with the separately audited finite coefficient decomposition and heterogeneous-carry clients rebuilt if necessary.

Let `V` be an IΣ₁ model, let the positive graph assignment and symbolic ports satisfy the literal zero hypotheses, and use one common witness `N,w` from the graph alignment/congruence theorem. Put `n = 8807*N`, `M = Exp.exp (67*n)-1`, `C = q-v₁-v₂`, `F = v₁`, and `ρ = Exp.exp 67`. First explicitly prove `0<n`, `0<M`, `C<Exp.exp (67*n)` and `F<M` from the graph hypotheses; these are required inputs, not implicit facts. The graph gives `((directK+w)*C)%M = F` only after the parameterized symbolic K is actually supplied to the congruence theorem, the model K cast is handled, and `q-1=M` is established. This specialization has not been compiled for the same-witness congruence theorem.

For T in the externally finite pair {4393,5495}, define standard-indexed model functions

```
f_T i = dig 67 C (cyc n k ((T-i) : V))       -- i : Fin 943
b_T j = dig 67 C (cyc n k ((T-position j) : V)) -- j : Fin 41
S_T   = Σ_i selector_i*f_T i + Σ_j (2^(10+j))*b_T j.
```

Use natural bounds `i<T` and `position j<T` to control subtraction before cast, and reduce each offset modulo n when applying `ArithmeticCyclicWord.dig_rot`; prove the associated cast/subtraction and model-index equalities rather than using native wrap arithmetic implicitly. The exact local target is the **partial raw-column identity** for the two reflected families:

```
raw_band T k = S_T
S_T = (Σ_i f_T i) + Exp.exp 10 *
      ((Σ_i (Exp.exp 41 - tileValue i)*f_T i) + Σ_j (2:V)^j.val*b_T j).
```

The second line is exactly `CompactCoefficientDecoder.finite_decomposition`, already paired/audited, after defining these f/b; it is for arbitrary model functions and does not itself prove the first line. Define a finite family with two copies of `Fin 943 ⊕ Fin 41` for reflected selector/copy terms, four one-weight bare terms at exponents 30,62,1100,2201, one spatial term at exponent 8807+42, and one temporal/fractional term. Specify the family coefficients and words explicitly, preserving duplicates as separate addends. Derive the complete raw equality `raw k = S_4393 + S_5495 + residual k` by finite-sum splitting and `dig_rot`; do not replace it by `raw k = S_T` without proving the other band's and residual terms vanish at that column.

For the radix-power K contributions, `ArithmeticCyclicWord.kernel_rotation_congr` relates the model cast of the finite power sum times C modulo M to the weighted finite rotations. Its hypotheses include `n>0` and `M>0`. The separate symbolic model-cast lemma still needs a concrete specialization or a parameterized graph interface; retained-byte equality is an additional obligation. The graph's factor w is `Exp.exp (R-67*n)`. There is no proven divisibility of that exponent by 67. Treat it as a **bit-level** rotation `rot 1 (67*n) C ((R-67*n) % (67*n))`, subject to the exact `rot` bounds and modulus identity, or state an explicit alignment hypothesis. Never silently make it a base-2^67 rotation or assume its digits are ≤3.

Propose a `CompactHeterogeneousCarry.CarryInput 67 n F b D a X` client for that full family: aligned C-rotations have digit cap 3 only after applying `dig_rot` to the graph's bound; the fractional/temporal rotation gets the full cap `Exp.exp 67-1` from the generic digit bound unless a stronger lemma is proved. Establish word bounds, weighted mass/slack (the audited conservative finite inequality is a candidate after the model cast), target bound, and the modular congruence separately. Then `carry_column` relates the complete raw sum and incoming carry to the corresponding digit of F. This is not yet a proof that a particular predecessor is clean.

To apply supported selector/copy bounds at k, separately prove the model residue identity `cyc n k (T-e) % 8807 = e` from `n=8807*N`, `k<n`, `k%8807=T`, and the standard index bounds. Split the case that the cyclic source index is zero: the origin has digit 1; for a positive source index, use the corresponding supported-selector/copy theorem. In particular, residue 1 must be shown absent without applying a positive-index lemma at zero. The external finite family does not bound model N or allow replacing arbitrary model indices with standard naturals.

The output high-mask no-carry fact must be transported to the target 67-bit digit and the high-mask digit at residue T, with the subtraction-by-one/origin condition checked. Even then the decoder needs `NoCarry S_T (2^51-2)`. This does not follow solely from `NoCarry (dig 67 F k) (2^51-2)` and `S_T ≤ raw k`: incoming carry, the other reflected band, the temporal word, and modular wrap can mask low-bit contributions. A sufficient interface may explicitly require zero incoming carry and zero residual at the chosen target, or prove a stronger exact low-limb identity. The previously recorded finite fractional-rotation witness shows that support/Boolean-anchor facts alone do not establish the desired clean predecessor. Existence of a suitable target, disjointness/overlap facts for the actual selector set, all-model word construction, local-to-global matching and machine simulation remain separate.
