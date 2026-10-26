# Independent review of the literal fifteen-coordinate parent in Lean

Reviewer: `/root/circuit_reduction`. The new Carrier66 module and checks
were authored by `/root/controller_certificate`. Verdict: **PASS within
the explicit canonical-parent scope**. No correction was requested.

## Frozen files

Paths are relative to `Computability/DiophantineConsistency/`.

| File | SHA256 |
| --- | --- |
| `Lean/DiophantineConsistency/Carrier66.lean` | `22ab116b489cacf7652dc490448e26e4aa1bc7735e35284c33449b0bf27a92eb` |
| `Lean/DiophantineConsistency/Carrier66Checks.lean` | `504bd0bf203ba56946087be89fb8390ff0af3423d68cdd4beb467fa49a03f7f2` |
| `Lean/DiophantineConsistency/Carrier65.lean` | `be2f2cb6833d190818541a57bb9b7c148c5975864d6af518f511b67f80fb1154` |
| `Lean/DiophantineConsistency/Carrier65Witness.lean` | `2b9324dc4594200c917b353b51a049815c0999beff31f26152d84e3fe0731f1f` |
| `Lean/DiophantineConsistency/FirstPellCarrier.lean` | `3e96510fa492760fe0876e2e230b9520c1429a20c7272c2a06b465b249ed859f` |
| `research/carrier65-independent/PROOF.md` | `53ec75050c7f4a00386d9738f8c515f3a816d8e4d94afcebb54b3497d972e749` |

I read every line of the final 280-line module and 51-line checks, and
compared the interface and both maps with the complete ordinary proof,
especially sections 1, 4, and 5. I had previously read Carrier65 and
independently reviewed ROOT's Carrier65Witness. I authored
FirstPellCarrier; this receipt reviews its use in Carrier66, and is not
an independent-author review of that prerequisite itself.

## Literal parent and coordinate maps

The parent has precisely the independent coordinates
`J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma`. The four ports remain
`beta,K,MC,MF_source`; no extra beta shift is applied. The added factor
is exactly `k-h*E-R`, with independent `h=v5` and `tau=v10`.
The output is the complete product `P*Q*U*index*W*Z-Delta`.

The implementation temporarily calls Carrier65's common blocks with
`n=1`, then replaces both `tau` and its first-norm factor `P`. The
generic-ring theorem `placeholder_irrelevant` establishes equality
with any placeholder value. Thus no dependent block retains the
placeholder or substitutes it for the independent first root. The
maps preserve all other blocks exactly. `drop` removes h and tau and
inserts n; `restore` inserts h and the derived first root. The actual
coordinate round trips and the entire polynomial identity under
`index=1` are proved, rather than checked only on sample witnesses.

The ring-map and evaluation theorems connect the literal parent value
to an actual integer `MvPolynomial (Fin 15)`. Focused checks bind its
index/rank expression symbolically, preserve the independent root,
check both coordinate inverses, and derive evaluation zero from the
explicit canonical predicate.

## Soundness and completeness scope

`Canonical` states exactly the five unit factors
`P=Q=U=index=W=1`, the scaled strong value `Z=Delta`, and `R>0`.
It is not inferred from an arbitrary parent product zero. This is the
canonical parent interface used by the retained ordinary completeness
argument.

For every positive Carrier65 zero under `PortBounds`, the forward map
uses the proved sign, rank-window, and positive-h recovery results.
It derives tau positivity and a positive omitted quotient before
constructing a positive canonical parent. `PortBounds.beta_min` is
the actual premise `31<=beta`, not merely beta positivity.

For the converse, a positive canonical parent plus `beta>0` supplies
positive E,Y,k,tau and positive R. The first-norm and index equations
are passed to `FirstPellCarrier.restore_carrier`, which proves the
new positive integer n and the exact first-root identity. Equality
of every remaining arithmetic block then proves the full Carrier65
polynomial is zero. No stronger native rank bound or independent
positivity of a derived expression is hidden in this converse.

Accordingly, the final endpoint equates positive Carrier65 polynomial
zeros with positive **canonical** parent polynomial zeros. It does
not classify all positive parent zeros, nor assume a native
consistency equivalence to prove this arithmetic result.

## Fresh verification

The reviewer ran both commands successfully against the frozen files:

```text
lake env lean Computability/DiophantineConsistency/Lean/DiophantineConsistency/Carrier66.lean -o /tmp/Carrier66-peer.olean
lake env lean Computability/DiophantineConsistency/Lean/DiophantineConsistency/Carrier66Checks.lean
```

The printed axiom lists for the coordinate, polynomial, forward,
converse, and final existence theorems contain only standard
`propext`, `Classical.choice`, and `Quot.sound` (with smaller lists for
the direct identities). No `sorry`, custom axiom, or `native_decide`
is present in the two new reviewed files.

These commands freshly checked the new module and focused checks;
they do not constitute a fresh rebuild of the entire ancestral
dependency closure. Literal operation counts/degrees, complete native
calibration, concrete port construction, and an internal-ZFC
consistency endpoint remain separate obligations. The present result
adds explicit arithmetic maps between the literal polynomials.
