# Rocq endpoint for the 224 — work in progress

Target: `Dense.halts dense_tm Dense.c0 ↔ StandardZFC ⊢TC ⊥` for the literal table of
[candidate-k224](../../candidate-k224/README.md). The files in `src/` compile against Elliot
Glazer's k230-rocq (`3142e4d`, Rocq 9.1.0), namespace `K224` (`tools/cc.py` compiles one file at a
time against the built reference).

## Done (each file compiles; the main statements are closed under the global context)

| File | Content |
| --- | --- |
| `Codes224.v` | The 224's bundle from its emitter contract: `bundle224 a b c = -. (kf224 -> (vrel -> -. helper224))`. Two conversion lemmas pin the contract: its original expression *is* `bundle230`, and its canonical expression is `bundle224`. |
| `Thm224.v` | The 224's calculus K′: `thm230` with the bundle replaced. |
| `Sound224.v` | **Soundness.** `thm224_thm230 : thm224 n -> thm230 n`. Each 224 bundle is derived from `bundle230 a b c` (K core via double-negation fusion, membership vacuity) and `bundle230 a b (wel a b)` (the helper). Hence `thm224_sound : thm224 1 -> StandardZFC ⊢TC ⊥`. |
| `CD224.v`, `Prop224.v` | K230's bundle-free logic proofs (`CD230`, the propositional part of `Comp_Prop230`), transferred by renaming (`tools/gen_prop224.py`). |
| `L224Def.v`, `L224Prop.v` | Jeff's pure-logic calculus `lprov`, with LB6a split into membership vacuity (any fresh binder) and the 224's helper (binder `wel x y`), plus his 71 propositional lemmas (`tools/gen_l224.py`). |
| `L224Meta.v` | Jeff's metatheory re-proved for `lprov224`: the deduction theorem, equality reflexivity bootstrapped from the helper, vacuity for equality-free formulas, and Leibniz substitution, specialization and alpha-renaming on quantifier-free membership matrices. |
| `L224E.v` | **The equality interpretation.** `Eind x y` (membership indiscernibility, auxiliary `S (x+y)`), the translation `th`, and `lprov_th : lprov a -> lprov224 (th a)`. This is the hard direction's equality-indiscernibility argument. |
| `Interp224.v` | `lprov224_thm : lprov224 a -> thm224 (tau a)`, the composite `lprov_thm224 : lprov a -> thm224 (tau (th a))`, and `kcore_thm224` (every enabled K core instance, via the fused core). |
| `Cert224Offsets.v` | The offset-bisimulation certificate (2,272 entries, 8 with register 5 offset) between the 224's literal source and `ptree dag224`. `dag224` is K230's `Dag230` with only the AX node 236 rebuilt to emit the 224's word (`tools/make_dag224.py`). The generator reproduces `Cert230`'s size (2,392 entries) on K230 itself. |

## Remaining

1. **Completeness.** `KPrimeOrdIR ⊢TC ⊥ -> thm224 1`: Elliot's `CompleteBase230`/`Complete230`
   with `Q a := thm224 (tau (th a))`. The K instance takes its private label from the
   *interpreted* matrix, `c := tau (th (Wn (Wn (tr source_names phi))))`, which is above 3 and
   not free in the named matrix.
2. **Program layer.** `Dag224.v`, the enumerator with `bundle224`, and the `ProgLib`/`L2Root`
   proofs re-run on `dag224`. The AX node's word uses only existing atom macros.
3. **TM side.** Regenerate the runtime forks (K labels 79, 140, 175, 191, 208, 229 disabled; boot
   409,835 steps), compose, and recheck with `coqchk`.
