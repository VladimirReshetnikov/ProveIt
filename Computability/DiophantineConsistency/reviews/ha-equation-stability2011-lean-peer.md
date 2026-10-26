# Independent exact-current HA stability binding review

2026-10-26. Reviewer: `controller_certificate`. Author: root.
Result: PASS, with no requested source changes. This review read both new
sources and the full author receipt, then freshly replayed both leaves in
an isolated overlay. No source, shared object, or Git operation was changed.

## Exact bindings

Paths are relative to `Lean/DiophantineConsistency/`.

| Source | Lines | SHA-256 |
|---|---:|---|
| `HAEquationStability2011.lean` | 34 | `ef2b90bb86d00541a03ff1647b8ce0d35ae2e1395438a04ab6f1f044f4a6810c` |
| `HAEquationStability2011Checks.lean` | 25 | `9808a8c56dfb7c51699e5145204aea94de9c82ec9ea50c5902111aa89f7cd23f` |

Author receipt `ha-equation-stability2011-author.md` has SHA-256
`cce1ac8ed34fc6c0e6ef74227cf0138e42d302a12e32ad939d88da8e4717daf9`.
The generic deduction/stability packet was independently read and freshly
replayed immediately before this binding; see
`ha-deduction-stability-lean-peer.md`, SHA-256
`6138238111a248c61dd77030be2723471c28feafb346f529e9670dc58f5bc760`.
The arithmetic compiler and literal-current binding were independently
reviewed and freshly replayed in `arithmetic-expression-lean-peer.md`,
SHA-256 `3e2e2400386fea4ba57dbfee174daa591d9079f61e140447bb52ebecd12ffb90`.

I did not author these new files, the compiler, or the HA deduction relation.
I did author the underlying literal `Carrier65` and kernel modules and
several native arithmetic prerequisites, as disclosed in the compiler peer
receipt. This is independent review of the new syntactic/logical binding,
not a new independent audit of every native theorem.

## Source review

`negative_unsolvabilitySentence` applies `Negative.neg` to the exact
`ArithmeticExpression.equation ObjectCurrentEquation2011.naturalExpression
Fin.val`, then uses `Negative.closeN 14`. The result is definitionally the
accepted `ArithmeticCurrentEquation2011.unsolvabilitySentence`, with its
actual successor-substituted fourteen-coordinate polynomial and four fixed
ports. It does not replace the polynomial by an arbitrary proposition or
assume that its natural evaluation is zero or nonzero.

`derives_stability` is an actual `HA.Derives []` proof of
`doubleNeg unsolvabilitySentence → unsolvabilitySentence`. The generic
negative-fragment theorem supplies the proof; no arithmetic facts are
needed. `Proves.of_derives` explicitly witnesses an empty supporting
arithmetic axiom list. The focused check repeats this over the axiom
predicate `fun _ => False`, and another check retains the actual sentence
closure theorem. The conditional `of_proves_doubleNeg` is genuine HA modus
ponens applied to this particular stability derivation and a supplied HA
proof of its antecedent. It is not unrestricted double-negation elimination.

## Fresh replay and dependency scope

Private overlay: `/tmp/ha-equation-stability-peer-controller-20261026`.
I reauthenticated all 135 inherited current-source records and copied the
133 accepted prerequisite primary objects from the previously reviewed
arithmetic overlay, its three independently rebuilt compiler/check leaves,
and the two independently rebuilt generic HA main leaves: 138 primary
objects in total. The two new target objects were absent before their
fresh builds. Source and copied-object pins were rechecked afterwards.
The inherited arithmetic objects retain their previously documented scope;
in particular this is not a fresh replay of the entire native source closure.

Both first independent attempts exited 0, serially, with this command
pattern and `Elab.async false` in both files:

```sh
lake env bash -c 'export LEAN_PATH="/tmp/ha-equation-stability-peer-controller-20261026:$LEAN_PATH"; exec lean -M6000 -j1 -o /tmp/ha-equation-stability-peer-controller-20261026/DiophantineConsistency/MODULE.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/MODULE.lean'
```

The main log is empty. The checks log has exactly four axiom reports, each
with only `propext`, `Classical.choice`, and `Quot.sound`. These are Lean
metatheoretic dependencies of the literal source binding, not extra
constructors or axioms in `HA.Derives`. Both fresh outputs are byte-identical
to the root's accepted objects:

| Object | SHA-256 |
|---|---|
| Main | `f4ffa81e715439f0f7db8e1ed7747423b8addc3a3271635b0606c924b8df7085` |
| Checks | `b66f4f2d3e9777a7ccf66d888b151fac8b5c4ac64936f562af6ab90a6cf75e44` |

The checks log has 526 bytes and SHA-256
`bcffbc2c338d9a8260d0cd12021c0b68f5d1e559a35845c5f632d42968afe1b6`.
Private `inputs.json` and `outputs.json` retain the exact evidence.
Toolchain and manifest hashes remain respectively
`2773c517aa90b66ea8a2c52bddddf84393157797f8341be0df45294fff7fd32e`
and `95e215b005fe9aacc1e5490c781d57e3044d2da5ca452495cfcd0e4eff908665`.

The accepted arithmetic dependency overlay includes older native object
graphs which omit the newer source imports `QuadraticFiber` and
`TotalDegreeBound`; that pre-existing limitation is not repaired or hidden
by these leaf replays. Source and object pins match the accepted evidence,
but a complete fresh current-source closure is a separate root job.
PASyntax and its authenticated five-module closure were also reused, not
rebuilt. No compiler or native source file was changed for this binding.

## Scope

This proves existence of an HA derivation of the exact-current sentence's
stability, `¬¬NoZero → NoZero`. It does not give an HA derivation of `NoZero`,
`Con(ZFC)`, or their equivalence. It supplies no PA-to-HA arithmetic
interpretation, internal machine-checker calibration, or target-translation
comparison. Those remain distinct obligations.
