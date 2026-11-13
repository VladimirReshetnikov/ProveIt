# Compact symbolic model ports for the natural-80 gamma route

`Natural80CompactModelPorts.lean` is an **unelaborated source proposal** for
the exact symbolic port representations and model inequalities needed by the
[80/107 gamma route](../ordinary14-natural80-gamma-model-route/README.md).
The source and its imported drafts have not been compiled. The checker below
pins 11 source files and inspects selected declaration signatures and calls;
it does not run Lean, check types, resolve providers, or prove the proposed
facts. The three `#print axioms` commands have not been executed.

For an `ORingStructure V` satisfying `𝗜𝚺₁`, the proposed `modelPorts` uses
natural casts of the *same* symbolic tuple as `CompactSymbolicModelIff.p`:

```
0: betaNat
1: paramKernel rho
2: lowNat
3: betaNat + highNat
```

Port 3 is already beta-shifted. The proposed `port_representation` states
for each slot that the signed integer symbolic port, cast into `DiffRing V`,
is the embedding of the corresponding model natural cast. It does not equate
this tuple to any physical P72/P115 file or the different Carrier65 PDF.

The proposed `port_bounds` states, **inside the model**, all seven facts

```
0 < beta, 46 <= beta, 0 < K0,
0 < MC, MC < beta, 0 < MF, MF < 2*beta.
```

The proposed derivation combines existing **source declarations**, some of
which are themselves unelaborated research drafts:

* `CompactPortBoundsSlimDraft.port_bounds` supplies beta positivity, beta at
  least 46, `MC<beta`, and `MF<2*beta`, after specializing its beta identity
  and the two fixed-mask identities. The referenced slim source is unelaborated.
* `StrictK0SymbolicDraft.kernel_model_pos` proposes `K0>0` using the kernel's
  isolated positive top term. That source is also unelaborated.
* For `MC>0`, `CompactConcreteMask.model_origin` identifies the least base-`2^67`
  digit of the model cast of `lowNat` with `Exp.exp 67 - 2`.
  Monotonicity and the standard cast of `2^2=4` make that digit positive. If
  the model cast of `lowNat` were zero, its digit would be zero; natural-model
  order then gives `0<lowNat`. This is a proposed model argument, not a
  numerical evaluation or an externally authenticated-byte theorem.
* `MF>0` follows from `beta>0`, natural nonnegativity of `highNat`, and the
  port-3 sum. The existing `scalar_rank_window` signature directly asks for
  `0<beta`, `MC<beta`, and `MF<2*beta`; the strict MC/MF positivity facts
  are included to match the external 80-graph port hypotheses explicitly.

Any actual proof requires Lean to verify the casts, `change`/`simp` rewrites,
order and digit lemmas, implicit instances, and all imports; it must also
complete the gamma-zero graph-to-norm argument and the iPRA client chain.
The port facts are **not** a Lean theorem until that happens. Model facts in
`IΣ₁` do not alone establish an iPRA proof. Symbolic-to-physical byte, graph,
and PDF associations remain separate.

An [independent source and mathematical review](../../reviews/ordinary14-natural80-compact-model-ports-independent/README.md)
checks the tuple, positivity arguments and cited rank assumptions without
elaborating the proposed declarations.

Run from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary14-natural80-compact-model-ports-draft/check_source.py | cmp - research/ordinary14-natural80-compact-model-ports-draft/result.json
```
