# Author receipt: uniform internal C222 seed image projections

Author implementation and self-review by `controller_certificate`,
2026-10-26. This is not independent peer review. The complete 138-line main,
53-line checks, exact invoked finite-deduction contracts and both private
drivers were read before execution. Both leaves passed their first capped
compilation, with no failed run, source correction or cap change.

## Mathematical scope

For every arbitrary internal IΣ1 model, labels `a,b,k` and matrix code `p`,
the literal closure now implies both

```
SUP = forall b (b in k -> exists a p)
COV = forall b (b in k ->
                ((forall k (k in a -> k in b)) -> req b k p)).
```

The proof normalizes the closure's negative universal into its actual
existential/conjunction code with the previously proved finite certificate.
Its left projection gives SUP. Its right projection, followed by the actual
rho6 certificate `ex_all_elim`, gives COV. No `Vac a p`, `Vac k k`, formula
well-formedness, semantic truth or generalization-under-an-assumption rule
is supplied. The input label `a` remains free in COV. This is not a claim
that an additional universal input binder has been derived.

`pair_image` combines these projections with the original root request.
`seed_image` gives the resulting existential at the self-labelled matrix
`p=c`, under exactly the actual seed gates `c != a,b`. Diagonal input/output
roles and legal `c=0` instances are retained.

The second half supplies finite implication/universal/negation congruence
certificates for the literal `req` and `clos` circuits. With the fixed
container label `pad p = not(not p)`, the two actual CProv implications
between `p` and `pad p` change only the matrix, without renaming that binder.
The numeric constructor bound `pad p > 3` proves the two gates at roles
`a=1,b=3` for every internal `p`, including zero. Consequently

```
matrix_image p : CProv (exists (pad p) (SUP and (req and COV)))
```

uses the original matrix `p` in all three clauses. Its witness theorem is
literally `exists code, ArithmeticHistory222.value code = formula + 1`.
Focused checks retain coincident binders, legal diagonal/zero seed gates,
the precise free-input coverage formula, all-internal and concrete zero
matrix witnesses, and the already-authenticated Nat adapter to actual C222.

These are actual internal checker witnesses. They are not raw-membership
CP/GIC, tagged comprehension, semantic seed validity, arbitrary represented
formula/proof translation, or a proof of the equation equivalence in HA.
The known external seed-to-ZF route uses tagged domains and augmented
separation; the old C254 bundle projections cannot be substituted here.

## Exact sources and fresh outputs

| File/module | SHA-256 |
|---|---|
| `ZFCinPA/ValidatorSeedImage222.lean` | `96c7b803fa0a11578545c8cabbdab6cd2b1321e21497f82ee895ce9610ecf511` |
| `ZFCinPA/ValidatorSeedImage222Checks.lean` | `b96821ce186a0b757994727c85c71e3f3c44bcc2d7c6cdc72318491010a35e72` |
| Main fresh object | `d0897f05fe806288ece2bf08b118922b2347758a5f6fd1f13750492415a62c54` |
| Checks fresh object | `8192fcb2ce831007aad777b1266af5fa109f77e29e032b82c83f2a76e4c2a8d2` |

Source root is `Logic/Interpretability/ZFCinPA/Lean`.
The complete durable inventory is
[validator-seed-image222-replay.json](validator-seed-image222-replay.json),
SHA-256 `d79bf3855cd650c5d4df1a80ce4460ad3c513f774038c92efad3ca1a32bec0a7`.
It records complete driver texts, current source/import/object pins,
commands, snapshots, logs, timings and all 14 axiom reports.

Private output: `/tmp/seed-image222-controller-pl30zl_x`.
Its pre-execution input inventory has SHA-256
`c3e8245548567965b2a97eb7b7008ba365051335f4aaad577ac3e695406ffa6c`.
Only the two new leaves were freshly compiled. The exact selected closure
reuses 128 authenticated custom modules, including 95 Foundation modules,
413 object/companion files and 38 explicit external boundaries, from the
accepted SeedClosure receipt
`a26ffb2dd781c1d863fcea15e0bc394baef8c80baf5997c2ba230897f17c7ccf`.
No Foundation or broad dependency rebuild is claimed. The private LEAN_PATH
has no shared project-cache fallback.

Each fresh command uses the pinned Lean 4.32 compiler with
`-M6000 -j1 -DElab.async=false`, producing only its private object. Main
completed in 3.55 seconds with an empty log; checks in 1.92 seconds. Maximum
RSS was 1,823,256 KiB. All fourteen reports contain only `propext`,
`Classical.choice` and `Quot.sound`. Before/after source and object hashes
matched. The 512 MiB disk reserve was enforced, with 910,045,184 bytes free
at the final inventory check. No accepted source, shared object or Git
state was changed by this packet.
