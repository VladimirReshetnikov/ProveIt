# Foundation first-index graph: concrete witness bound

`PRAFstIdxWitnessBound.fstIdx_bnd_succ` proves over every IOpen model that
Foundation's exact `fstIdxDef` graph implies its exact `bnd` transformation at
bound `p+1`. The proof extracts the two existing witnesses, bounded by `p` and
by the first witness; the remaining `subDef` and `pairDef` matrices are open.
The graph is a concrete subformula used in `derivationOf` and the derivation
blueprint. It is not a bound for the other proof, formula or schema witnesses.

`candidate_fstIdx_bound` proves the corresponding mapped result in every
candidate-PRA model, and `candidate_proves_fstIdx_bound` is an actual
candidate-PRA proof of its universally closed source-language instance. No
Σ₁ collection or IΣ₁ model assumption is used. This does not construct a
`BoundCertificate` for Foundation's full ZFC refutation sentence ρ, prove its
literal consistency equivalence, or compare candidate PRA to a standard PRA
presentation.

The author build `/tmp/pra-fstidx-bound-u9rcqqll` passed both source/check
modules and final authentication. `inputs.json` pins both sources, the accepted
34-module provider state and its entire recorded local parent graph, and the
specific inherited Foundation HFS Basic source/object pair. `parent-manifest.json`
retains the authenticated parent manifest. Source snapshots, full compiler
logs, terminal state and exact commands are in `author/`. Foundation, Mathlib,
and other transitive package dependencies remain inherited; merely hashing the
specific Foundation pair is not a full source-current audit of Foundation.

For an independent replay against the accepted provider run:

```sh
python Computability/DiophantineConsistency/reviews/pra-fstidx-witness-bound-author-replay/replay.py \
  --parent /tmp/pra-after-open-bound-merge-independent-vc0ixiig/lib \
  --expected Computability/DiophantineConsistency/reviews/pra-fstidx-witness-bound-author-replay/author/state.json
```

The replay checks parent graph sources and objects, the fixed Foundation
source/object pair, the two client sources before and after, and source,
object and full-log hashes against the author records. The second check module
prints the Lean axiom dependencies; output and all commands are preserved.

Both independent replays passed: root `/tmp/pra-fstidx-bound-2qkpaz2k` and
private `/tmp/pra-fstidx-bound-q_lot4xz`, each with matching source, object
and full-log hashes for both modules. Their snapshots, logs and states are
retained in `root/` and `private/`. The theorem bounds the standalone exact
graph; binding it after substitution inside the larger refutation sentence
remains separate.
