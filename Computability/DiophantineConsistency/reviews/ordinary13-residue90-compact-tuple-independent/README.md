# Independent bounded source review of compact tuple clients

No concrete mismatch was found in the reviewed source. The first client uses
`K = CompactSymbolicKernelOpaque.paramKernel CompactSymbolicKernel.rho`, with
`rho=2^67`. Unfolding its local ports gives the same symbolic natural tuple as
`CompactSymbolicModelIff.p`: beta, that K, low, and beta+high, followed by an
integer cast. The local irreducibility attributes in the source defining `p`
are local to that source; the new client itself does not add such an attribute.
The proposed `rfl` is plausible from these source definitions but remains
unelaborated.

The second client's equality has the correct direction: chosen ports equal
`p`, while `byteP_eq` states `byteP=p`, so its symmetry supplies `p=byteP`.
The original byte source decodes each Lean list via `Nat.ofDigits 256` into a
natural before casting to an integer. Its assembly's fourth list is already the
shifted-high list, and the source theorem identifies its value with
`betaNat+highNat` exactly once. The endpoint source does use the same symbolic
`p`; the inspected equalities do not identify the residue-90 graph with that
endpoint's graph. The arbitrary-K theorem requires the stated explicit
`K=chosenKernel` assumption.

The original deterministic receipt reproduced during this review. The
independent checker pins the reviewed bytes and checks the relevant definitions
and theorem directions, plus elementary tuple controls. These checks do not
run Lean, authenticate transitive providers, validate external byte files or
a PDF, establish graph bridges, or establish an iPRA equivalence. Existing
`#print axioms` commands are source text, not reported axiom results.

Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-residue90-compact-tuple-independent/check.py | cmp - reviews/ordinary13-residue90-compact-tuple-independent/result.json
```
