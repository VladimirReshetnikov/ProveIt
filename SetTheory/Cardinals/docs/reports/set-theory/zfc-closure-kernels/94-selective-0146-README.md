# Assignment-only equality completion and trace certificates

Research contribution dated 18 October 2026 for the ProveIt ZFC busy-beaver project.

## Main result

The equality-as-predicate completion of source44 FC15* can retain function
congruence only for assignment evaluation `V` and assignment update `C`.
The omitted class constructors `N,A,Q` are reconstructed by their incidence
contracts. Witness constructors `W,Y,Z,H` are forgotten before the quotient
and then reconstructed using raw applications to least-code representatives.
The model proof handles the raw and reconstructed meanings of the nested
member selector and coded extensionality term separately.

| Native theory | Completed clauses | Completed literals | Template bits |
| --- | ---: | ---: | ---: |
| Published FC15* completion | 29 | 82 | 1616 |
| Five-base control (`V,C,N,A,Q`) | 25 | 67 | 1351 |
| Assignment-only FC15* (`V,C`) | **22** | **58** | **1195** |
| Also reconstruct guard `G` | 21 | 54 | 1148 |
| Also derive reflexivity from native01 | **20** | **53** | **1134** |
| Published FC16* completion | 30 | 86 | 1823 |
| Five-base extensional control | 26 | 71 | 1558 |
| Assignment-only FC16* | **23** | **62** | **1402** |
| Also reconstruct guard `G` | 22 | 58 | 1355 |
| Also derive reflexivity from native01 | **21** | **57** | **1341** |

The assignment-only reduction saves 421 bits. Reconstructing the variable-keyed
guard `G` removes another 47 bits. Explicit equality reflexivity follows from
native01 and the retained left-Euclidean equality law, removing 14 more bits.
The final targets save **482 bits** using the exact existing four-bit prefix term format.
Counts include equality completion and omit the refutation solver, universal
interpreter, register implementation, binary runtime and blank initializer.
All nine function tags remain in the ground term enumeration. No new binary
machine or measured state saving is claimed.

`skolem_reduct_body.tex` contains the complete ordinary model reconstruction
and finite-search equivalence proof. It can be included in the main delivery
report. `skolem_reduct.tex` is an optional standalone wrapper. The new
equisatisfiability argument is self-contained; the final comparison with
`Con(ZFC)` explicitly invokes the accepted native FC15*/FC16* calibrations.
This is not a Lean or Coq proof-assistant result.

The note also proves a negative boundary: FC15* with only the `E`-congruence
completion row removed has an explicit infinite model constructible in ZFC,
even retaining all nine original function-congruence rows. It therefore loses
the desired calibration (assuming consistent ZFC). The new targets retain
`E` transport. This countermodel fails the added FC16* clause and gives no
automatic conclusion about that stronger variant.

## Reproduce the finite artifacts

Requires only Python 3.10+ and its standard library:

```sh
python skolem_reduct.py --output skolem_reduct_results
```

The script checks pinned input hashes, regenerates the exact clauses, writes
JSON/bit-string/packed-byte payloads, and verifies their prefix decoding with
the independent source44 decoder. Its quotient-certificate checker retains
only the two assignment-function tags. A full-tree implementation independently
checks its congruence results on 1,440 sampled finite labelings.

The local `W`, `N` and `V` controls distinguish omitted and retained congruence.
They have empty native clause lists and are not finite models of the theory.
Native stages `k=0,1` have no retained instances and are staging regressions.
Both native `k=2` stages have 12 retained clauses; the inherited witness
`2097728` is accepted and the zero candidate is rejected. The `k=2` stage has
56 candidate bits; this test does not exhaust that range. Resource errors
propagate and are never converted to UNSAT.

An optional `raw_guard=True` checker mode uses term-code-indexed `G` values,
while `E` and `Inc` remain class indexed. This uses the same `B²` guard table
field and permits different `G` values on one equality class, as checked by
a separate two-literal fixture. For the final reflexivity-deletion target,
the finite-label stages still impose structural reflexivity. The proof states
this as an admissibly strengthened sequence: reflexivity is globally derived,
although its derivation can leave a particular small code interval.

`skolem_reduct_results/results.json` records the exact metrics, payload hashes,
finite controls and their scopes. `.bits` files end in a newline; reported
payload SHA256 values hash the pure bit string without that newline. `.bin`
files are big-endian streams with the explicitly reported trailing zero pad.

## Trace-commutation support

`trace_commutation.tex` proves that closed halt-free register fragments commute
when neither writes any register tested by the other; shared additive outputs
are allowed. The generic disjoint-register trace approach is already present
in ProveIt intake163/source66 and source67, so no general novelty claim is made.

`trace_commutation.py` derives effect footprints from the frozen AST, computes
lexicographically least topological normal forms, emits adjacent-swap
certificates, and checks them independently. Run it against the original
`zfc245-proof-20261018` package inputs:

```sh
python trace_commutation.py --inputs INPUTS \
  --grammar INPUTS/state_reduction/route-grammar.txt \
  --output trace_commutation_results.json
```

The pinned 128-rule grammar has 162 strict disjoint and 211 additive-output
independent pairs after excluding halt atoms `J,n`. Neither relation merges
any already-existing key. Search outcomes and any binary compiler validation
belong to the parent report and are not inferred from this normalizer check.

## Provenance

ProveIt input commit: `6446ff5668307a2ac6aee1896037f0b792090389`.

The `reference/` files are byte-exact copies from that checkout:

- `ground_kernel.py` from `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/44-nine-code-ground_kernel.py`.
- `coded_extensional.py` from the same directory's `44-nine-code-coded_extensional.py`.
- `finite_class_closure.md` from `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/44-nine-notes-finite_class_closure.md`.
- `LICENSE.ProveIt` from the repository license.

Their expected SHA256 values are hard-coded in the reproduction script and
included in the result. Source44 and its earlier finite class/assignment and
EPSC dependencies retain their original attribution. The finite quotient
certificate representation adapts the existing
`Computability/BusyBeaver/Research/ZFC/finite_quotient_frontend.py` experiment.

`SHA256SUMS` covers this contribution's report source, code, references and
results, excluding Python caches and the manifest itself.
