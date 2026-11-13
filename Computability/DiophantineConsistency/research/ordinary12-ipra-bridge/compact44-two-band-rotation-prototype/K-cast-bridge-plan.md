# Exact symbolic K cast needed by the two-band theorem

This is a source-only proof plan. The statements below have not been compiled against a common provider. Work in a type `V` with `[ORingStructure V]` and `[V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`, after building the symbolic-kernel modules and the two-band module on one coherent provider. Open the namespaces used by those sources. The exact missing declaration target is:

```lean
theorem symbolic_kernel_band_cast :
    ((CompactSymbolicKernelOpaque.paramKernel CompactSymbolicKernel.rho : ℕ) : V) =
      CompactPartialBandRotation.kernelBand (V := V) CompactSymbolicKernel.position 4393 +
      CompactPartialBandRotation.kernelBand (V := V) CompactSymbolicKernel.position 5495 +
      TwoBand.bareKernel (V := V)
```

The natural `paramKernel rho` and its model cast are the specific K selected here. This target is not a statement about an arbitrary K and does not bind the symbolic expression to retained bytes or the displayed equation. The companion `CompactSymbolicKernelLink.kernel_eq_param` equates the separately defined symbolic `kernelNat` and `paramKernel rho`; its own provider dependencies still need joining, and that equality alone does not establish retained-byte binding.

A small intermediate target for every **standard** natural exponent avoids computing the enormous powers:

```lean
theorem cast_rho_pow (e : ℕ) :
    ((CompactSymbolicKernel.rho : ℕ) : V) ^ e =
      Exp.exp ((67 : V) * (e : V))
```

Unfold `rho` only to the symbolic power `2^67`, not to its numeral. The chain is `((2^67 : ℕ) : V)^e = ((2^(67*e) : ℕ) : V) = Exp.exp (((67*e : ℕ) : V)) = Exp.exp ((67 : V)*(e : V))`. The existing `ArithmeticStandardCasts.cast_exp (V := V) (67*e)` proves the middle conversion; standard cast-of-powers, `pow_mul`, and cast-of-products provide the other steps. This uses an external `e : ℕ`, not a claimed theorem for every internal model exponent. The proof must avoid simplifiers that evaluate `2^(67*e)` for the concrete large offsets.

Apply `CompactSymbolicKernelOpaque.cast_paramKernel (V := V) rho`, and use `cast_rho_pow` for the four bare powers and each exponent in the two finite sums. For the spatial factor, first use the standard power-addition identity to combine `rho^8807 * rho^42` into `rho^(8807+42)`, then convert the standard exponent to 8849. Do not reduce 8849 to 42 without a separate cyclic-modulus argument. Distribute each selector/copy coefficient over its two reflected powers and split the `Finset` sums; regroup the four resulting sums into the definitions of `kernelBand position 4393` and `kernelBand position 5495`. Identify the five bare entries with `TwoBand.bareKernel` by finite index reasoning while keeping the powers opaque.

For selector index `i`, the model exponent in either band is exactly `(((T - i.val : ℕ) : V))`; for copy index `j`, it is `(((T - CompactSymbolicKernel.position j : ℕ) : V))`. Both subtractions occur in `ℕ` **before** casting. The proved `CompactSymbolicKernel.row_lt_target` and `position_lt_target` give the standard bounds below 4393, hence below both targets, if their intended reflection interpretation is later needed. The cast bridge itself need not rewrite these expressions into model subtraction or assume any unproved subtraction identity.

Once the declaration above and `TwoBand.combined_congr` are available in the same provider, instantiate its `pos` with `CompactSymbolicKernel.position`, its model-valued `K` with the cast in the displayed target, and its `hK` with `symbolic_kernel_band_cast`. The theorem still requires `0<n`, positive `Exp.exp (67*n)-1`, and the explicit model graph congruence `(((K:V)+w)*C) % (Exp.exp (67*n)-1) = F`. Obtain these from `CompactSameWitnessSaturation.fixed_graph_saturation` applied to the **same natural K**, using its same `N,w`: set `n = 8807*N`, identify port 1 with K via the definition of `CompactSymbolicPorts.ports`, and prove `Exp.exp (67*n)-1 = v 0*(p 0:V)` from the returned `q` identities, with positivity inherited from that same witness. These are additional proof obligations, not consequences of the cast lemma alone.

The output still contains the separate `w*C` term. No divisibility of the exponent defining `w` by 67 is assumed, and no claim is made here about full columns, decoder carries, retained-byte/display equality, machine equivalence or an internal iPRA proof.
