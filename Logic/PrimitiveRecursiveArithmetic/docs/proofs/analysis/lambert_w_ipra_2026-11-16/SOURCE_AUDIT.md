# Source and reuse audit

## Primary target

- Wikipedia, **Lambert W function**, accessed 2026-11-16.
  `https://en.wikipedia.org/wiki/Lambert_W_function`

The source page was treated as a claim inventory, not as a proof authority.
Every mathematical formula used in the report is either rederived, supplied
with explicit constructive side conditions, marked conditional, or placed in
the deferred/audit class. A notable correction is the formula
`W_0(-pi/2)=i*pi/2`: the argument lies on the conventional principal cut, so
the equality requires an upper-boundary value convention.

## ProveIt revision inspected

- Repository: `https://github.com/VladimirReshetnikov/ProveIt`
- Main commit inspected late in the audit:
  `f444b76e8480ebea128c15b4a59f158e14f478cc`
- Date of that commit: 2026-11-16.

The repository can advance independently; the SHA above records the interface
snapshot used for this packet.

## Reused ProveIt material

1. `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`
   - `PR`, `PTm`, `PRAAx`, `PRA.qfInd`.
2. `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Deduction.lean`
   - intuitionistic derivability `Prf`.
3. `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean`
   - `NFm.ofPRA`, `pra_iff_native`.
4. `Logic/PrimitiveRecursiveArithmetic/docs/proofs/algebra/lagrange_inversion_ipra/`
   - finite truncated-series fixed points, finite Laurent residues,
     Lagrange–Bürmann, Lambert coefficients, and radius architecture.
5. `Logic/PrimitiveRecursiveArithmetic/docs/proofs/analysis/trigonometric_identities_ipra_2026-11-15/`
   - rapidly convergent rational names, exponential tail bounds, constructive
     `pi`, and finite analytic identity methodology.
6. `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/lambert-w/Lambert_W_Guide/`
   - broad Lambert W theorem inventory, applications, and numerical context.

The packet restates the needed arguments so it remains readable on its own;
reuse concerns architecture and proof components rather than blind citation.

## External mathematical background

The bibliography in the TeX report names the foundational Corless–Gonnet–Hare–
Jeffrey–Knuth paper and DLMF for historical/source orientation. No external
computer algebra result is used as a proof. `mpmath` values in the verifier are
only diagnostics after exact formulas have been derived.

## Audit policy

- **F**: a finite bounded identity or combinatorial theorem suitable for direct
  quantifier-free induction.
- **A**: a constructive analytic theorem on rapid names, with explicit or
  algorithmically specified error/tail moduli.
- **C**: conditional on an external effective theorem whose proof is not
  developed here.
- **P**: partially reconstructed or stress-tested, not claimed in full.
- **D**: deferred, corrected, historical, software-specific, physical-model,
  or otherwise outside the native theorem set.

The complete 82-item classification is in `THEOREM_LEDGER.md` and
`claims.json`.
