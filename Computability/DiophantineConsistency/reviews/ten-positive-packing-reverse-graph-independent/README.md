# Independent review: conditional packing to reverse graph

`TenPositivePackingReverseGraph.packing_seed_zero` is a semantic theorem over an arbitrary `IΣ₁` ordered arithmetic model. It takes a natural tuple `p`, model values `K,N,stride,sY,n,eta,zeta,gamma,w,t,r`, and a **Σ₁-definable** model function `word`. It assumes one exact packing and seed tuple:

```text
PackingInput 590069 K low high N stride word
SeedRelations (590069*N) (2*r+1) sY n eta zeta gamma
```

along with these exact model port equalities:

```text
(p 0:V)=Exp.exp 590069 - 1     (p 1:V)=K
(p 2:V)=low                     (p 3:V)=high + (Exp.exp 590069 - 1).
```

It also assumes positive `(p 0:V)`, `sY,w,eta,zeta`, `4≤r`, `(2*r+1)%4=3`, and the exact rank, power and transport equations

```text
rank K N stride word = 2*r+1
Exp.exp (590069*N)*w = Exp.exp (2*r+1)
(K+w)*Cw 590069 N word = Fw 590069 K N stride word
                            + t*(Exp.exp (590069*N)-1).
```

In particular, this adapter's port 1 is required to equal the same K used by the packing; this is stronger than merely saying it is unconstrained. The theorem does not derive the listed inputs from a halt or a 90-zero. Its conclusion is only `∃ v : Fin 10 → V, (∀j,0<v j) ∧ InternalZero (graph (integerPorts p)).output v`.

The proof uses the same `K,N,stride,word` throughout. It first forms the **intermediate** source valuation `![rep 590069 N, Fw 590069 K N stride word, alpha 590069 K N stride word, 1,1,w,sY,1,1,1]`. The packing facts prove positivity and mask; they identify q, the rank and X/Y for that source and convert the explicit transport to the reverse graph's natural transport hypothesis. It unfolds the same supplied `SeedRelations` to recover both unscaled interval equations; its extracted `r0` is explicitly identified with the assumed r. It derives the 72r size bound from `4≤r`, then applies `ScaledReverseGraph.graph_zero_of_source`. The final zero witness is produced by that separate theorem, not asserted to be the displayed intermediate valuation; no coordinate-preservation equalities occur in the exported conclusion.

The conclusion is conditional on the exact shared packing, port and seed assumptions. It does not itself provide a machine-to-packing implication, a 90-to-80 implication, formal JSON/PDF coefficient binding or a syntactic iPRA proof. In particular it does not prove that the externally retained original 80 coefficient is the packing K; the known kernel discrepancy remains separate.

`check.py` checks accepted `observations/graph-attempt03/terminal.json`, current and copied source, runner, output and logs against recorded hashes, scans the accepted source for `sorry`/`admit`, and resolves the first object for each of its two source-direct imports against runner pins. The selected `ScaledReverseGraph.olean` hash matches the independently reviewed reverse-graph packet; exact paths and hashes are in `check-output.txt`. The accepted object SHA is `aa879b5d70f582eedce7f0d0665d916c3703fb33540925411d96520e746c021e`; author log reports `[propext, Classical.choice, Quot.sound]` and no error, warning or `sorryAx`. Earlier failed scratch attempts are not evidence. No Lean replay was performed; transitive object selection, source-object, package and dynamic provenance remain inherited.
