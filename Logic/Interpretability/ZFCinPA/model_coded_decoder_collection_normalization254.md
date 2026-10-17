# Exact logical form of the numerical G circuit

The checked normalization retains all original numeric labels, including c as
both the decoded input formula's code and the outer container binder. Its
literal native formula is

```
nativeG(a,b,c,p) = exists c.
  (forall a. a in b -> forall b. p -> exists b. p and b in c)
  and (forall b. b in c -> exists a. p).
```

The module proves `decoded(bundleG a b c) <-> nativeG(a,b,c,decoded c)` in
actual internal ZF, for arbitrary internal a,b,c. It also proves congruence
in p under the explicit actual named-GEN resource. This identifies formulas;
it is not a proof of G. No gate is needed for the equivalence, while the later
G proof must retain both c!=a and c!=b and handle a=b separately.

The source reuses the checked circuit normalizer, logical conjunction and
existential equivalences, and the C module's congruence helpers. It never
relabels a variable with a decoded value. Provable equivalence under named
binders permits the later code-zero reduction to Top without falsely saying
that literal decoder0 has no free0.

The focused Lean4.32.0 source and audit pass 3 ordered axiom reports and 6
callers with only standard Lean axioms and zero warnings. Both commands took
1.869 s. The selected closure contains the checked C object and its 54 actual
project prerequisites, six external boundaries/discovery anchors, and actual
Init/Std/Lean/Omega first providers. All 137 input/provider and fresh-object
postchecks pass. The exact inherited same-source Cantor bf2-selected and
ff1-unselected artifacts remain separately attested; they are not silently
interchangeable providers. No new Slots object is imported by this module.

The first attempt compiled the unchanged source, but its audit omitted the
namespace defining `decoded` and failed. That attempt, its recovery timeout,
and exact source/audit/guard are preserved. Only the second attempt is an
overall PASS; its sole repair is the audit's namespace open. No heartbeat,
memory, thread, or dependency change was made.

From the repository root, with the pinned dependencies and recorded objects:

```sh
python Logic/Interpretability/ZFCinPA/check_model_coded_decoder_collection_normalization254.py \
  --repo "$PWD" --dependency-root /path/to/pinned/Proofs \
  --output /external/fresh-output
```

`--prepare-only` performs no proof build and still queries `lean --version`.
The guard supports explicit source/audit, exact C evidence/source/audit,
project and namespace caches, compiler, and library paths. An optional
`--unused-cantor-object` relocates the exact unselected historical artifact;
it does not change the selected bf2 object. No dependency is built or fetched.

The separate checked `CompiledCollection254` module now supplies the translated
fixed Collection proof with its schema and equality callbacks discharged. The
pending G client must prove the exact typed substitution bridge to that result. For
positive c, own-code freshness justifies the container binding; zero and
coincident-label cases remain explicit. This checkpoint supplies no G or
bundle provability, accepted-proof translation, PA consistency comparison,
binary simulation, or state-count claim.
