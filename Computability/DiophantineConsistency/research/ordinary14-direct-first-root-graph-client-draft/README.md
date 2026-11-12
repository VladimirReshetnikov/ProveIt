# Source-only 84↔79 graph first-coordinate client

`GraphFirstRootClient.lean` is an **unelaborated source proposal**: no Lean process or kernel check has run. It proposes a fixed-other-coordinates positive-root existence comparison between the literal 84 and 79 graphs, conditional on the separately drafted generic model lemma. It is not an established graph theorem, global positive-zero equivalence, iPRA endpoint, provider replay, degree proof, or external PDF/JSON/gzip binding.

The three bare imports refer to source drafts in `../ordinary14-qcube84-lean-draft/P84QcubeGraph.lean`, `../ordinary14-direct-pell79-lean-draft/P79DirectPell.lean`, and `../ordinary14-direct-first-root-model-draft/FirstRootBridge.lean`. Their import paths are a proposed future overlay layout; this packet does not create one, authenticate direct/transitive providers, or establish compatible object ancestry. Each imported source is itself uncompiled.

## Explicit proposed statements

For `ORingStructure V` modeling IΣ₁, a positive natural beta and slot-zero value, and the explicit port representation `(p 0 : DiffRing V)=ι beta`, the client defines q, X, Y, ell, scale `M=q³*(J*beta)`, `P=ell+k`, and `D=1+ell*(ell+k)`. The definitions use only slots 0, 6, 7, 9 and 10; slot 8 is updated by `Function.update`. The proposed source includes proofs for:

* literal equality of the other four graph fields and their independence from slot 8;
* positivity of M from beta and J, positivity of D, and positivity of a replacement valuation when all original coordinates and the replacement are positive;
* exact `DiffRing V` evaluation of the 84 first residual as `M²*((P−r)²−D)` and of the 79 first residual as `r²−D`, with the beta cast hypothesis and natural/ring distinction explicit; and
* `positive_first_coordinate_iff`, an existence comparison over positive replacements at slot 8 with the other thirteen coordinates held fixed, by the generic five-square lemma.

The other port values are arbitrary integer leaves, but the explicit p0 representation and positivity hypotheses must be supplied. The fixed-other-coordinate theorem by itself does **not** assert that all thirteen other coordinates are positive: a global positive-valuation existence client still must use `putRoot_positive` and prove the update-back identity. Nor does it identify the symbolic beta with compact44 bytes.

The source tactics (`simp`, `ring`, `change`, coercions and `InternalZero`/`Expr.evalRing` rewrites), graph definitional equalities and reduction/resource behavior have **not been tested in Lean**. The exact identities, dependency analysis and 100 small exact integer controls in `check_source.py` are external checks only; they do not establish model truth or elaboration. The statement may require a corrected proof or new source lemmas once a guarded compiler is available.

## Still required

Before compilation, independently review this source and the pinned graph/generic statements; build a coherent overlay with exact source, object, Init and transitive provider routes; verify the existing disk/resource guards and obtain the exclusive Lean allocation. After a successful local proof, construct the all-coordinate-positive existential client and the remaining 84↔85, 85↔86↔87↔88 and endpoint model bridges. The 84 route still needs its modified-carrier source replay, compact Mersenne port, and internal Pell projection-quotient lower bound. None is supplied here.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-direct-first-root-graph-client-draft/check_source.py > /tmp/first-root-graph-source.json
cmp /tmp/first-root-graph-source.json research/ordinary14-direct-first-root-graph-client-draft/observation.json
```

Independent source review is recorded in
`../../reviews/ordinary14-direct-first-root-graph-client-draft-independent/`.
