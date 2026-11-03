# Four closed byte recipes decode to the symbolic port tuple

`CompactFourPortByteAssembly2.decode_ports` proves in Lean that pointwise
base-256 decoding of the closed tuple

```
![RetainedBetaBytes.betaBytes, CompactKernelByteRecipe.bytes,
  CompactLowByteRecipeData.bytes, CompactShiftedHighByteWindow.bytes]
```

equals `CompactSymbolicPorts.ports betaNat (paramKernel rho) lowNat highNat`,
whose four components are `[betaNat, paramKernel rho, lowNat,
betaNat + highNat]`. The fourth port contains the beta shift **exactly once**.
The proof specializes the separately checked abstract four-list mapping
lemma with the four already checked natural decoding equalities, rather than
reducing the large lists during a finite-index proof.

The selected 631-file union adds the generic mapping object to the prior
four-port union. The prior preflight compared all selected shared files and
companion families across the MC, MF and K providers; no shared file had
different bytes and no foreign companions were suppressed. This retry's
preparer rechecked the earlier manifests, recorded provider paths and direct
guards, pinned the generic source/object/log and its direct guards, rejected
a conflicting overlap, and created a fresh single root. The bounded author
wrapper and Lean run `observations/attempt01` exited 0 in 1.879 seconds
without warnings or `sorryAx`; direct guards, selected files and all recorded
producer source/object/log/receipt and provider paths remained unchanged at
the checked points. Source SHA-256:
`597a60517cd5563b21c96077cbead4e5f213ae8a01feac65099fd1512f4dc65a`;
object SHA-256:
`0f921668ce8407f4a28346a85e2023d131fc4421e00c790048ac2d813f8e3a85`.
Lean's `[propext, Classical.choice, Quot.sound]` report lists metatheory
dependencies, not iPRA axioms.

The [first direct tuple attempt](../compact44-four-port-byte-assembly-prototype/README.md)
hit kernel memory and produced no object. This success concerns **Lean byte
recipes**, not Lean proofs about filesystem files or gzip. The recipe/source
transcriptions were checked externally against pinned retained parent
payloads; the parent-to-95-row-supplement relation, PDF transcription and
compact iPRA endpoint remain separate. This is one author-side mixed-provider
build, not a paired replay or complete symbolic/project/package/dynamic
ancestry audit; guard checks are point-in-time.
