# Source-only Lean route for the guarded 89/26 graph

This packet is a **source draft and proof trace, not a Lean result**. The
literal `P89GuardedGraph.lean` is generated from the reviewed 89-row JSON;
its proposed `output_shape` has not been parsed, elaborated or kernel checked.
No model bridge, endpoint, JSON/PDF semantics, total-degree theorem or new
proof of consistency is asserted. In particular, the separately proposed
88/30 parent model bridge and its 88/46 predecessor are themselves
**uncompiled drafts**. Existing author-side free-J endpoint and recorded
provider routes retain their stated ancestry and dynamic-load limitations.

## Literal graph stage

`make_graph.py` pins the candidate SHA, checks all 14 witness names and four
ports, and writes the 89 literal rows as `Expr (Fin 14)` with a proposed
`P89Guarded.output_shape`. `--check` verifies byte-identical generation and
never invokes Lean. The names and row order are source-level checks, not a
Lean theorem that an external file or straight-line program has that meaning.

A first guarded compile would need to verify imports, `.var 13`, the `guard`
identifier, definitional equality and resource behavior. No runner or Lean
launch is included here.

## Model-wise positive-zero bridge: remaining work

For `V` an `ORingStructure` satisfying `IΣ₁`, use the existing `DiffRing V`
embedding for subtractions. A genuine internal bridge needs **both** witness
maps in every model, rather than an appeal to the external standard-integer
proof:

1. Generate a signed-fold/guard graph client and exact ring-evaluation lemmas
   relating its common residuals and Bt to `P88FourSquare.graph`, using a
   `Fin 14`/`Fin 13` variable projection with the first-root coordinate
   changed. From `output_shape`, use nonnegative-square extraction, as in
   the proposed `P88FourSquareModel.zero_iff`, to get all four residuals and
   `Bt=ι(h)>0`. Graph equality and `Fin` index lemmas are new clients.
2. From the signed first norm, obtain positive-scale quotient roots and
   internal `q³∣Y` and `b∣Bt`, where `b=J*beta`, `q=1+b`. Existing
   `ArithmeticAdaptiveQuotients2011.scaled_quotient` works in every IΣ₁
   model for natural `m,z,n`, `0<m`, `z*z=m*m*n`: it explicitly calls
   `ArithmeticSquareDivisibility.dvd_of_square_dvd` and returns both a
   quotient and its square equation. For signed ring expressions, first
   represent the root by `ArithmeticSignedPairs.magnitude` or
   `P72Root.ι_magnitude_sq`; an ordinary prime-valuation proof over ℤ is
   **not** by itself an arbitrary-model proof. `FreeJRootBinding.root_rep`,
   `first_scaled_norm` and `folded_quotient_forces_Y_divisible` show a
   relevant positive/negative-pair technique, but target the old literal
   and cannot be invoked on the signed graph without a new representation
   and adaptation. The b|Bt congruence and transfer through the modified
   first expression are also new obligations; `P72Root.first_root` and
   `ArithmeticModularCancellation` are references, not direct clients of
   this graph.
3. The main quotient similarly uses `scaled_quotient` after an appropriate
   signed-magnitude representation. A new internal consecutive-squares lemma
   must rule out `k=2`: then eta=zeta=1, c=2Y+1 and the main radicand lies
   strictly between consecutive squares. For k>2,
   `ArithmeticPellFirstNorm.positive_parameter_solution` supplies an
   internal first-Pell index; one must show the index is at least 2 and
   prove the positivity/cast side conditions. The existing
   `CompactSeedOrdinate.seed_ordinate_le_k` then supplies `s<=k` from
   `Y=s*q³` and that index. Alternatively use
   `ArithmeticPellFirstNorm.descent` to formalize the reviewed elementary
   descent; the external bound is not already a theorem for this graph.
4. For the **guarded→parent** direction, `Bt>0` and b|Bt give a positive
   quotient t. Once q−1>=2 and s<=k,
   `CompactFirstPositive.positive_first_carrier` constructs a positive old
   first input from the Pell norm and t; an exact relation `Bt=b*t` must be
   fed to the ring client. Its q−1>=2 hypothesis is automatic at compact44
   beta but is stronger than the external generic beta>0 proof for b=1.
   Finally build a positive `Fin 13 → V` witness and transfer the remaining
   three residuals and output. There is no direct call to the uncompiled
   parent `zero_iff` until this graph-specific construction is supplied.
5. For the **parent→guarded** direction, use the old parent-to-`FreeJ13`
   source route and `FreeJ13Halt.forward` only after compiling their draft
   clients. `FreeJFirstTransport.freej_first_factor_transport` then proves
   the old positive input's Bt>0; `FreeJRootBinding.first_root_quotient` and
   `first_factor_forces_Y_divisible` provide the corresponding old-literal
   roots and Y divisibility. An internal b|Bt lemma and root sign/client are
   still needed. Construct `h=Bt` and the opposite-root sigma from the
   external proof, after proving `t<ell` with the port bound below. Transfer
   the unchanged residuals and check all 14 coordinates positive.

The draft `P88FourSquareModel.positiveBridge` proposes the eventual model
endpoint for the parent, but neither it nor the 88/46 clients have been
elaborated. After a new model-wise guarded equivalence is actually checked,
its bridge may be composed with those clients and the existing endpoint
adapters. Standard integer same-zero results alone do not supply this
IΣ₁-model result or an iPRA derivation.

## Internal compact44 port bound

The external equivalence uses `beta>0` and `0<=K0<(beta+1)²`.
`CompactFixedBeta.beta_identity` identifies the symbolic beta-plus-one with
`Exp.exp (67*8807)` in each relevant model, and
`CompactFixedBeta.bounds` supplies beta positivity (with positive J).
`CompactCellProductBound.symbolic_kernel_lt` gives the symbolic
`paramKernel rho < Exp.exp 592884`; the available `exp_add` and `exp_monotone_le`
lemmas can be used to build a **new** internal lemma
`paramKernel rho < (beta+1)²` from `592884 < 2*(67*8807)`. Its natural cast,
port-index correspondence and the inequality `K0*q<q³` must still be proved
at the exact model/DiffRing interface. The byte-payload equality to symbolic
ports remains an external binding, not a Lean file/PDF theorem.

Only after source review, compatible dependency/provider and companion route
checks, independent guarded preflight, the established resource/disk limits,
and explicit exclusive allocation should any Lean test be considered. The
generator is not a prelaunch or provider-closure audit.

```
python3 -I -S -B research/ordinary14-guarded-fold89-lean-draft/make_graph.py --check
```

Independent source review is recorded in
`../../reviews/ordinary14-guarded-fold89-lean-draft-independent/`.
