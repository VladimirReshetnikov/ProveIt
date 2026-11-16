# Lean formalization plan

Pinned upstream: `VladimirReshetnikov/ProveIt` commit
`8649990597d73657bde480b6c389de7f85bc0cb0`.

## Status

No `lean` or `lake` executable was available in the artifact runtime.  None of
these files was compiled here.  `NativeClauseFramework/Bridge.lean` contains no
`sorry` and is intended to be the first candidate checked in the pinned
workspace.  The blueprint files contain explicit proof holes and are not
presented as formalized results.

## Recommended location

Add the modules under:

```
Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/
  NativeClauseFramework/
```

and import them from the existing `IPRADerivations` Lake library.  This keeps
all public endpoints in `Prf PRAAx` and permits direct reuse of
`IPRADerivations.Core`.

## Dependency order

1. **Bridge**
   - imports `ConciseIPRA.NativeClausalDiagonal` and
     `ConciseIPRA.NativeBiInterpretation`;
   - proves `cutAsmList`, `cutOne`, `exportPRA`, `importPRA`;
   - acceptance: no `sorry`; compile; audit axioms.

2. **Program**
   - dependent `Node` and `Program` types;
   - `Program.compile` by induction and `cutAsmList`;
   - sparse dependency variant using indices;
   - acceptance: compile two-node and five-node closed examples.

3. **Algebra exchange smoke test**
   - import a checked theorem from `IPRADerivations.Geometry.TriangleFormulas`;
   - compose a native equality/substitution node;
   - export to the exact ordinary formula;
   - compare the theorem statement after round-trip rewriting.

4. **Restricted Boolean language**
   - equality, Boolean operations, bounded `all` and `any`;
   - characteristic `PTm` compiler;
   - object-level equivalence theorem;
   - avoid a universal formula evaluator.

5. **Trace and search**
   - generic `TraceSpec` using `IPRA.ind`;
   - bounded folds, least search, complete enumeration, finite tables;
   - exact success and failure contracts.

6. **Finite coding layer**
   - choose one pair/list/table encoding;
   - projection, update, length, fold equations in `Prf PRAAx`;
   - abstract API so applications do not expose encoding arithmetic.

7. **Demand**
   - fixed-dimensional vector code, order, join, rank;
   - bounded monotone closure in `Prf PRAAx`;
   - reverse DAG demand pass;
   - backward schedule / forward replay.

8. **Relational**
   - cloud predicates, edge tables, reverse viability;
   - least path, exact observer, rational diameter, motion tail, gap recovery.

9. **Domains**
   - integer order, extensional rationals, dyadics;
   - finite matrices/polynomials;
   - represented-real operation contracts.

10. **Packet migration**
    - choose one moderate packet with an explicit finite theorem and producer;
    - replace its local host claims by actual direct or native derivations;
    - maintain a theorem ledger and axiom audit.

## Exact upstream declarations used

- `Cl`, `Cl.asm`, `Cl.toN`
- `KPrf`, `KPrf.subst`, `KPrf.cut`, `KPrf.toNPrf`
- `kprf_iff_nprf`, `kprf_iff_nprf_of_qfree`
- `NFm.unQ`, `NFm.toPRA`, `NFm.ofPRA`
- `native_iff_pra`, `pra_iff_native`
- `LeanProofs.IPRA.ind`, `LeanProofs.IPRA.inst`
- `ipra_ring`

## Proof-hole count in this archive

Run:

```sh
grep -RnhE '^[[:space:]]*sorry[[:space:]]*$' lean/NativeClauseFramework
```

Expected result at delivery: 17 occurrences in blueprint files and zero in
`Bridge.lean`.  The exact count is also recorded in `lean/STATUS.md` after the
build audit.

## Axiom policy

New checked modules should contain no `axiom` declarations and no `sorry`.
Metatheoretic uses of `Classical.choice`, `propext`, and `Quot.sound` should be
reported with `#print axioms`, following the existing `IPRADerivations` audit.
The public theorem must remain an explicit `Prf PRAAx` or `KPrf` judgment.
