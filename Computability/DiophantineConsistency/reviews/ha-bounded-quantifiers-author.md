# HA bounded quantifiers: author receipt

26 October 2026. **Frozen, fresh main/check PASS.** The author is
`circuit_reduction`; this receipt is not an independent review. The new
286-line main and 56-line checks import only the accepted strict-interval
leaf and its existing dependency closure. No frozen source changed.

The literal definitions are:

```text
dec a    = a ∨ (a → ⊥)
ball t a = ∀ (ltFormula(var0, rename succ t) → a)
bex t a  = ∃ (ltFormula(var0, rename succ t) ∧ a)
```

Slot zero of `a` denotes the bounded witness; its other free slots are
ambient parameters. `t` is an outer term, so every free variable of that
term moves under the new binder. General renaming/substitution identities
are proved for both bounded quantifiers. `plus a = rename(up succ) a`
preserves the matrix's witness slot while inserting the induction-bound
parameter outside it. The checked instantiation identities retain arbitrary
nested binders and sparse free variables; no closed-matrix hypothesis occurs.

The empty universal and the negation of the empty existential are proved
inside conventional HA. Each successor law is proved in both directions:

```text
ball (S t) a  ↔  ball t a ∧ a[t]
bex  (S t) a  ↔  bex  t a ∨ a[t].
```

These are separate actual HA implications, not a semantic equivalence used
as a proof oracle. The proofs use the literal strict-interval split and
Leibniz equality elimination. All open assumptions shift through each
universal/existential eigenvariable rule.

The central proof applies the actual `Arithmetic.induction` schema to
`dec(ball var0 (plus a)) ∧ dec(bex var0 (plus a))`, under the finite context
`[all(dec a)]`. In the successor step this context becomes
`[all(dec(plus a))]`. Instantiation at the current induction variable gives
`dec a`; the induction hypothesis decides the previous finite interval.
Finite intuitionistic conjunction/disjunction cases, and the successor
implications, decide the larger interval. The zero and successor substitutions
of the entire induction body are explicit checked identities.

The resulting endpoints are genuine conventional HA proof-existence results:

```text
HA.Proves ((∀ x, dec a) → dec (ball t a))
HA.Proves ((∀ x, dec a) → dec (bex  t a)).
```

The uniform premise is an object-language formula. It is neither an external
family of decisions for standard numerals nor a model `ProperOn` hypothesis.
There is no general DNE, Markov rule, positive Σ1 DNE, or conversion from
classical PA provability. The checks include nested all/ex matrices, sparse
slots 0/4/7, open and shifted finite contexts, empty and one-element bounds,
and arbitrary unrestricted matrix syntax under the stated uniform premise.

The complete draft main/checks, prerequisite interfaces and replay driver
were read before execution, and the final complete main/checks were reread
after the successful run. The first main compile failed on elaboration of
the local `inst`/`plus` aliases and negation membership, plus an unused simp
argument. Its exact source, log and null-object result remain in attempt
`1793064200140203489`; checks were not executed in that attempt. Fixes only
made the existing substitution identities and context membership explicit;
no statement or hypothesis changed. The second pair passed in 2.214 and
1.626 seconds. The final main log is empty and all 17 reports use only
`propext` and `Quot.sound`. No new axioms, `sorry`, `native_decide`, or semantic
arithmetic oracle was added.

The private output directory is
`/tmp/ha-bounded-quantifiers-author-fjx3lptt/lib`. Lean 4.32.0 was run with
`-M6000 -j1 -DElab.async=false`, actual source paths and fresh regular outputs.
The driver enforced a 512 MiB disk reserve. It independently traversed the
selected current source imports and authenticated 100 cached modules,
76 Foundation modules, 328 cached artifacts, 34 explicit external boundaries
and 607 deduplicated pre/post pins. No reused module imports the two new
leaves. Only the two new leaves were compiled; Foundation and external
packages were not rebuilt, and no shared object was overwritten.

The direct parent primary is the independently accepted root Intervals
object, SHA `acbacc7febae8c2a1b392ca005caf573b877f64285fa0dd285dc026defe83dee`,
under root record
`921b453155a52f99a404e0378b0bf6865ec6297b698196a0293f54c43ae77840`.
Earlier authenticated dependency primaries/available companions, explicit
external source/object records, compiler, toolchain and Lake manifest are
reused and pinned exactly; this is not a fresh whole-closure proof replay.

Final pins:

- Main: `43b5a74f24985cf6c3232504f074eab315b39edda0aa688af9cc3a76e006fe21`.
- Checks: `8b7fe74a1c8dc2a97b90b31a2154f3f94e67f9a12cc763dbeb8e82eb8be52db5`.
- Main object: `5aef4873ce228ef55ac107f2fb0c251da951552feee7d0acb92f0ca3061a992f`.
- Checks object: `713757dc3731f93cfaf3832b39cb78a21e401c2e547be42e8c51a14f09a86bbd`.
- [Replay summary](ha-bounded-quantifiers-replay.json):
  `8e0ecf97530c441611f1a46568d35fb3c7666929f6cef858af56314ce3abc0ec`.
- [Nineteen-file manifest](ha-bounded-quantifiers-replay/FILES.json):
  `7465b39cb6ee141df8fbdbff0163f1100d47faef0a0e3b7af66e34987a821688`.
- Final result: `d89896109ecad59ebef693b909ec0a0da0ecef8adf391e8f147532659c154925`.
- Final inputs: `2b2430c27cb271232144f4722bddb215b2a46ab1f4e8f9fd62395b8fb2abfe86`.
- Driver: `7d616252a092e04b53310abd628ca5de786d39df8ae67962213ba1366305ca95`.

Structural bounded-formula decidability, Foundation bounded-syntax/GG
comparison, and normalization of the actual proof checker are later tasks.
This packet does not identify a Δ1 representation with an HA-decidable
formula, prove arbitrary Π1 stability, or claim the target HA consistency
equivalence. The earlier read-only plan is
[the bounded-quantifier/checker audit](../research/ha-bounded-quantifier-next-leaf-audit.md).
