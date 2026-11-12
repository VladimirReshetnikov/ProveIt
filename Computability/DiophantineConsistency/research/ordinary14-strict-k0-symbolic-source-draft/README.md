# Symbolic K0 positivity: source-only proof route

`StrictK0Symbolic.lean` proposes proving that the selected symbolic K0
port is strictly positive in the models used by the natural-81 bridge. It
is **unelaborated source**: neither its proof scripts nor its imports have
been checked in this packet. The checker pins the source files and checks
their relevant declaration shapes; it does not run Lean or establish a
theorem. This route is separate from the external P72/P115 byte-positivity
test and does not prove that the symbolic integer equals those bytes.

The source route uses these exact existing declarations:

* `CompactSymbolicKernel.rho : ℕ := 2^67`.
* `CompactSymbolicKernelOpaque.paramKernel : ℕ → ℕ`.
* `CompactKernelSplit.kernel_split_generic (r : ℕ) :
  paramKernel r = r ^ 8849 + lowerKernelAt r`.
* `CompactSymbolicPorts.ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]`.
* `CompactSymbolicModelIff.p : Fin 4 → ℤ`, defined by casting
  `ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat`.

Because `rho>0`, its 8849th power is positive and the remaining summand is
a natural number. The proposed `kernel_nat_pos` proves
`0 < paramKernel rho` without expanding the kernel. For
`V` with `[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`, the proposed
`kernel_model_pos` applies `Nat.cast_pos` to obtain
`0 < (paramKernel rho : V)`. The proposed `port_one_representation` and
`port_one_pos` then identify the difference-ring cast of symbolic port 1
with the embedded model cast and transfer its strict positivity.

If elaborated, these lemmas would supply the stronger `K0>0` model premise
needed by the proposed 81 and shifted-Pell 82 forced-J graphs. The graph
transport, unit argument in the model, proof of equivalence in iPRA, and
symbolic-to-physical coefficient binding would still be separate work.

An [independent source review](../../reviews/ordinary14-strict-k0-symbolic-source-independent/README.md)
checks the split, port position and existing cast pattern without elaborating
the proposed lemmas.

```
python3 -I -S -B research/ordinary14-strict-k0-symbolic-source-draft/check_source.py > /tmp/strict-k0-source.json
cmp /tmp/strict-k0-source.json research/ordinary14-strict-k0-symbolic-source-draft/result.json
```
