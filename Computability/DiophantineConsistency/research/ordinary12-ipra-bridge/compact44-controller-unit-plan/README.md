# Proposed compact44 controller-unit proof

This is a source-level plan and an external finite calculation. It does **not**
prove a model-level unit, connect the retained coefficient bytes to the Lean
kernel, construct a graph zero, or establish an iPRA derivation.

The old [`ArithmeticConstructionUnit`](../../../Lean/DiophantineConsistency/ArithmeticConstructionUnit.lean)
provides a reusable proof pattern, but its constants and kernel are those of
the 2011 equation. For compact44 put `d=590069`, `p=581197`, `L=d*p`,
`rho=2^67`, `B=2^d`, `K=DC+B*DR`, and

```
Gamma(N,w) = rho^1063 * ((B^N)^2 - 1) * (1 + B^N * (K + B^w)).
```

For model naturals `m,e`, the intended dimensions are `N=p^(m+1)` and
`w=p^e`. The desired conclusion supplies `GammaInv` with
`Gamma(N,w)*GammaInv = 1 (mod d*N)` in every model of IΣ₁. This is one of
the explicit premises of the existing compact controller theorem; it alone
does not supply the selected tableau or its safe dummy locations.

## Finite residues to formalize

The accompanying `check_residues.py` evaluates the retained *recipe*, using
modular arithmetic throughout, and checks the following residues modulo
`L=342946332593`:

| quantity | residue |
| --- | ---: |
| `B` | 290226301192 |
| `rho^1063` | 298529384010 |
| `B^2` | 201792753151 |
| `DC` | 313772214412 |
| `DR` | 158651740298 |
| `K=DC+B*DR` | 284898815895 |
| `Gamma`, after `B^N` and `B^w` are replaced by `B` | 306697999258 |

It also checks `B^p = B (mod L)` and
`306697999258^(p-1) = 1 (mod L)`. These checks reuse the recipe's
transition table and coefficient construction; they are not an independent
transcription audit, and they do not connect the recipe to
`CompactSymbolicKernelOpaque.paramKernel` or retained/displayed bytes.

## Intended model argument

1. Prove the displayed `B`, `rho^1063`, and kernel residues in Lean. The
   kernel calculation should use the finite weighted-list representation and
   modular exponentiation, rather than expand the 592,000-bit integer. The
   symbolic-kernel digit theorem does not itself supply this modular identity.
   Establish the exact equality between this symbolic kernel and the `K`
   used in the model expression before applying the residue.
2. Follow `ArithmeticConstructionUnit.B_frob_iter`: transport the standard
   identity `B^p ≡ B (mod L)` into the model and use Σ₁ induction to obtain
   `B^(p^n) ≡ B (mod L)` for all model `n`. This supplies both `B^N` and
   `B^w` for the stated power-of-`p` dimensions. Handle the natural
   subtraction in `(B^N)^2-1` using its **positive remainder**
   `201792753151`: the old `sub_one_res` requires this stronger condition,
   not merely positivity of `B^N`.
3. Combine the residues to get `Gamma ≡ 306697999258 (mod L)`. Lift the
   finite power identity to `Gamma^(p-1) = 1+d*p*v` for some model `v`.
   Apply the existing `ArithmeticControllerLift.lte` with `c=d` and the
   odd base `p`, and use the explicit inverse
   `Gamma^((p-1)*p^m-1)`. This is the same exponent-lifting argument as the
   old unit theorem, with compact constants; no unproved model CRT or
   nonstandard prime factorization is needed.

No Lean execution was performed for this plan. The calculation can be
reproduced from the repository root with `python3` on `check_residues.py`;
optimized Python is rejected so its assertions cannot be disabled.
