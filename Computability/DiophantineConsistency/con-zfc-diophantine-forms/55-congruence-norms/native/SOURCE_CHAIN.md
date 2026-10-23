# Native coefficients and inherited semantic dependencies

This directory is the selected dependency bundle for the new equations. Its
repository source pin is ProveIt commit
`4b4349064a750ba6347293b55874a7f92abdd0db`. `SOURCE_MANIFEST.json` records every
copied source's repository path, SHA-256, Git blob identity, and size. Earlier
pins appearing inside preserved manuscripts identify those manuscripts' own
antecedents; they do not silently change this bundle's selected coefficient tuple.

## Reproduce the finite coefficients offline

From the delivery directory run:

```sh
python3 -B native/verify_native.py
```

Or, from this directory:

```sh
python3 -B verify_native.py
```

Python's standard library is sufficient. The verifier copies the coefficient
recipe to a temporary directory, executes its bounded construction, compares
all four regenerated integer magnitudes byte for byte, checks their recorded
hashes and bit lengths, compares the finite geometry/rank receipts, checks the
literal machine projection, and inventories the included formal import closure.
It neither runs the machine nor invokes a proof compiler. It writes
`VERIFICATION.json` with its actual check results.

The original generator can also be run directly:

```sh
python3 -B coefficients/build_coefficients.py
```

This materializes unsigned little-endian `.bin` integers and deterministic gzip
counterparts under `coefficients/payloads/`, and refreshes its binding manifest.
Gzip wrapper bytes can depend on the Python/zlib implementation; the uncompressed
integer bytes are the authoritative mathematical data.

### The single coherent tuple

The instance is **wang943-mixed-121x8801**, with

\[
 \rho=2^{121},\quad d=121\cdot8801=1,064,921,
 \quad B=2^d.
\]

| Polynomial port | Generator port | Definition | Bit length |
|---|---|---|---:|
| `beta` | `beta` | \(B-1\) | 1,064,921 |
| `K0` or `K` | `K` | \(D_C+B D_R\) | 1,070,004 |
| `MC` | `MC` | native data mask | 1,064,921 |
| `MF` | `MF_source` | \(MF_{native}+B-1\) | 1,064,922 |

All four ports belong to this same instance. In particular, `MF` is already
shifted. The four decompressed magnitudes total **533,099 bytes**. The recipe
first reconstructs the exact 943 Wang tiles from the literal 430 machine
actions, then computes finite sums of fixed powers. It does not depend on an
answer to the halting question or on any existential witness.

The fresh bounded verification passed all four byte comparisons, all **69,230**
support-overlap identities, the 989-position support conditions, exact carry
and population bounds, and the stated finite prime/order/unit checks for the
actual-rank controller. These finite checks establish the arithmetic facts
they explicitly test; the unbounded interpretations are supplied by the proofs
listed next.

## The mathematical implication chain

The selected chain is

\[
 \text{positive source zero}
 \iff \text{marked periodic Wang computation}
 \iff \operatorname{Halt}(K215,\mathrm{blank})
 \iff \text{a finite ZFC refutation exists}.
\]

Negating this chain gives the stated equivalence with syntactic
\(\operatorname{Con}(\mathrm{ZFC})\). The coefficient generator alone does not
prove any of these unbounded equivalences.

1. **The native tuple and its completeness promises.**
   `coefficients/COEFFICIENT_PROOF.md` gives the selected 121-by-8801 recipe,
   no-carry inequalities, support identities, mask populations, and the
   arbitrary-odd-factor controller for the *actual* packed rank. Its predecessor
   arithmetic is preserved in `coefficients/upstream/24-coefficients.tex`,
   `25-COEFFICIENT_PROOF.md`, and `27-COEFFICIENT_PROOF.md`. The fuller language
   and interface arguments are in
   `proofs/ordinary_native/wang943_language.md`,
   `mixed125_full_interface.md`, and `fixed_factor_padding.tex`.
   Historical coefficient values in those predecessors are not additional
   choices for this delivery.

2. **The marked language means the literal blank computation.**
   Sections 1–2 of `wang943_language.md` give every tile, both arbitrary-period
   soundness and helical completeness, including the direction/write on the
   transition into halt and every seam. `BLANK_HELICAL_PROOF.md` preserves the
   older window-language proof and the source of its padding/rank argument.
   The present tuple uses the 943-tile language, not that older enormous window
   alphabet. The verifier checks that the supplied transition JSON is exactly
   the dense table `calibration/k215.tm`, with initial state 0, working states
   0–214, halt 215, and blank symbol 0.

3. **The arithmetic source.**
   `proofs/parent_quartic31.json` is the literal 31-positive-variable,
   22-quadratic source used by the new selective compiler. Its SHA-256 is
   `1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287`.
   `QUARTIC31_SOURCE_PROOF.md` supplies the packing-register elimination.
   `ORDINARY_BLANK_PROOF.md` and `PELL_LEMMA_AUDIT.md` give the ordinary strong-rank,
   signed-auxiliary, power-recovery, half-binomial and canonical-converse steps.
   `SOURCE31_ADAPTER.md` spells out the direct connection of the literal
   31-variable equations to that ordinary interface, so no unbundled
   quartic32 register listing is needed to understand that connection.
   The specifically used Pell, inverse-population, synchronization, and dummy
   control manuscripts are also retained in `proofs/ordinary_native/`.
   These are universal mathematical arguments, not finite simulation claims.

4. **The exact K215 calibration.**
   `calibration/proof.md` is the accepted ordinary machine proof.
   `source_calibration.tex` contains the all-natural command compiler, raw-code
   soundness invariant, and cofinal successful enumeration above the actual
   cutoff 4. `PERMUTED_SOURCE_PROOF.md`, `PARTIAL_SELECTOR_PROOF.md`, and
   `DOMINATED_CALCULUS_PROOF.md` explain its predecessor transfers. These
   expositions inherit the numerical-calculus/ZFC calibration. The complete
   project-source closure for the exact external Lean endpoint is included
   under `k215_formal/`, as described below; the ordinary calibration is not
   being replaced by an assertion about a bounded startup simulation.

## Complete project sources for the K215 formal endpoint

The endpoint is

```text
SetTheory.BusyBeaver.ZFC.KEndpoint215.blank_halts_iff_zfc_refutation
  : BlankHalts machine215 ↔ BProv ZFCax_s [] Form.fBot
```

Its negated companion is `nonhalting_iff_zfc_consistency`. Neither theorem
takes consistency as a premise. The included Lean files contain the machine,
source/compiler, simulation, initialization, numerical calculus, and logical
calibration dependencies of that endpoint.

The bundled upstream import-inventory routine finds **168 project modules**
at this exact repository pin, plus the **two explicit endpoint clients**
shipped alongside the serial builder. All project imports are supplied; the
only external source boundary is Lean's shipped `Init`. The retained historical
README discusses earlier 176- and 204-module checkpoints. Those are historical
counts, not the count asserted for this selected closure.

With the pinned Lean toolchain already installed, the offline rebuild command
is, from this directory:

```sh
python3 -B k215_formal/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/build.py \
  --repo k215_formal --out /tmp/conzfc-k215-kernel-rebuild
```

The output directory must initially be empty. The preserved driver creates a
separate workspace, compiles modules serially, preserves logs and failures,
checks both clients' axiom reports, and uses the upstream shared compiler lock.
`k215_formal/lean-toolchain` pins the toolchain. The toolchain binaries and
their `Init` objects are not redistributed here.

**This delivery did not run that kernel build.** It verified exact Git blob
identities of the included sources and recomputed the complete import inventory.
`UPSTREAM_FORMAL_STATUS.md` and `UPSTREAM_LEAN_REPRODUCTION.md` preserve the
repository's inherited build claims and instructions; they are not fresh build
receipts from this session. A formal proof of the *new final Diophantine
equations* is also not claimed.

## Imported Jones nine-ratio contracts

`proofs/nine_ratio/NineRatio.lean` contains the full proofs of
`Jones1982.Nine.ratio_sound` and `ratio_complete`, in terms of the literal
`Vars` formulas and `Conds`. `Ratio.lean` supplies the ratio construction and
`ProductPell.lean` the associated square/product machinery. Their byte identities
were checked against this bundle's repository pin. The numerical contracts are
summarized in Section 4 of `MULTITARGET_NINE_PROOF.md`; the new delivery's own
proofs establish its modified source bounds and finalizer.

These three proof files are supplied for precise inspection, but **their full
transitive Lean/Mathlib import closure is not included**. Kernel replay of the
Jones ratio development uses the pinned full ProveIt HilbertTenthProblem Lean
project. This is the remaining external *formal replay* dependency of the
ratio branch. It does not affect bounded offline regeneration of the fixed
native integers, or the completeness of the separately included K215 project
source closure. The ordinary Diophantine adapters are inherited mathematical
proofs; they have not been newly checked by a proof-assistant kernel here.

## Attribution and preservation

`LICENSE` is the repository's MIT-0 license for new repository material.
`licenses/` preserves package31 and K215 notices and the inherited Wade license,
including the original-machine and normalized-source notices and the immediate
partial-selector/command-permutation attribution. The source manifests preserve
the distinction between source authors, machine ancestry, and the present
assembly and audit. No whole incoming archives, alternative machine candidates,
optimizer histories, or unrelated research packets are included.
