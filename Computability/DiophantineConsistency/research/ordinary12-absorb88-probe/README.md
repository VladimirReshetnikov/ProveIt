# Speculative 88-operation absorbed-root graph

The candidate replaces the 89-row graph's `g31=(ell+k)+r` by a new independent positive witness `r`; the old-to-new map is `r_new=ell+k+r_old`. The separate `g30=ell+k` remains used in the first norm. The digest-pinned `check-dag.py` checks exact source rows, slots, topology, all-live count and 100 exact forward samples: 88 binary operations, comprising 50 multiplications, 21 additions and 17 subtractions. Its retained output is `observations/dag-attempt01/result.json`.

`Absorb88Graph.lean` checks the three residual identities for the forward map over any commutative ring. The guarded author run `run-graph.py` passed in session 26946, exit 0, with source, provider pins, commands, resources and output under `observations/graph-attempt01/`. This is not an independent Lean replay; selected-provider and inherited package/dynamic/source-object ancestry limitations apply.

The [first-factor packet](FIRST.md) extracts the scaled norm and a positive
first Pell root from a full graph zero. It does not establish transport
positivity or the reverse direction. The [signed-root packet](SIGNS.md)
checks both first-root alternatives assuming the transport bound explicitly.

The later [signed-divisibility theorem](../ordinary12-absorb88-signed-divisibility-draft/README.md)
works directly from an actual positive 88 zero and proves `b ∣ q(Bp−Bn)`
in the model difference ring for either first-root sign, without assuming
transport positivity. A [checked corollary](../ordinary12-absorb88-signed-unscaled-draft/README.md)
removes the factor `q`, giving `b ∣ (Bp−Bn)` in that ring. It does not prove the positive normalization needed for
the reverse direction or a halt/iPRA endpoint. The recorded direct-provider
and historical ancestry limits remain.

The proposed reverse idea is to use divisibility `Bt=b*t` and the positive first-root branch to show `r_new=(1+k*b)*t+first>ell+k`; for the negative branch, reflection by `2*first` should preserve the whole graph and produce a witness above that threshold. Those claims have not yet been bound to this actual graph in Lean. Neither bounded-port model equivalence, halt, iPRA, nor a PDF binding is asserted for the 88 graph.

There is a substantive gap in that reverse plan: the existing 89 transport proof establishes `Bt>0` using the lower bound on the old expression `ell+k+r`. The new witness is only positive, and the actual 88 first residual permits `Bt<0` and a witness below `ell+k`. `check-obstruction.py` evaluates the actual pinned DAG with all witnesses and ports 1 except `r=251`: it obtains `ell=256`, `k=2`, `Bt=-2`, `Z=257`, and `A0=0`, while `r<ell+k=258`. The other two residuals are nonzero, so this does not refute full-graph soundness, but the first residual alone cannot supply the needed transport inequality. An argument using additional graph constraints is required.

The checker also verifies an independently supplied `Bt=0` example that satisfies the 90 comparison's symbolic port inequalities: `beta=3`, `K0=1`, `MC=MF=0`, `J=1`, `F=2`, `alpha=w=s=eta=zeta=1`, and `r=32769`. It gives `ell=32768`, `k=2`, `Bt=0`, `Z=98307`, and `A0=0`. This does not establish the other residuals or the actual fixed `K0`.

The `F,alpha` symmetry preserving `G=alpha+(q-F)b` suggests trying to normalize witnesses until `Bt>0`. The checker records an isolated first-factor obstruction: with the same bounded ports and `J=w=s=eta=zeta=1`, taking `F=1`, `alpha=19`, `r=32461` gives `q=4`, `G=28`, `Bt=-132` and `A0=0`. For `q=4`, any positive `F',alpha'` with `Bt'>0` must satisfy `F'+alpha'<4`, which gives `G'≤11`; thus this first-factor example has no such `G`-preserving normalization. Again, the other residuals are nonzero, so this does not rule out a normalization theorem for full graph zeros.

The independent [symmetry analysis](../../reviews/ordinary12-absorb88-transport-obstruction/README.md)
also gives an external conditional construction: from any fixed-port 89 zero
it obtains a full 88 zero with negative transport, using the checked fixed
coefficient bound `K0<beta²`. It does not assert that such a zero exists or
disprove equivalence of the two zero-existence statements. It does show that
universal transport positivity is not a viable reverse route in the stated
conditional setting.

A subsequent author check has proved conditional reverse existence and unrestricted forward existence; see `CONDITIONAL.md` for the exact 88-side transport hypothesis and check evidence. The arbitrary-zero, halt, and iPRA questions remain open.
