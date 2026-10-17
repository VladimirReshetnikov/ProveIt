# Internal exchange of two named universals

Three narrow Lean checkpoints prove the actual numerical rho4 row for arbitrary
internal labels and matrices, including equal labels and the literal decoder's
zero implication alias. The last theorem is

```text
Provable T (decode (ArithmeticTemplates254.rho4 a b c))
```

for every actual Δ1 set-language theory `T`, every model of IΣ1, and every
internal `a,b,c`. It needs no set-theory axiom, GEN resource, freshness condition,
closed matrix, or standard-code restriction. This is one logical row; it is not
the full C254-to-ZF interpretation, a represented proof selector, or a
PA consistency comparison.

The first checkpoint, `ModelCodedBindOneSwap`, defines a fixed Σ1 graph for
`swapVec d = qVecIter d [#1,#0]`. Its total Δ1 function fixes every old bound slot
below internal depth `d` and exchanges exactly the new slots `d,d+1`. Actual
Π1 syntax induction proves, for `IsSemiformula L d p` and distinct labels `a,b`,

```text
subst L (swapVec L d) (bindOneAt L a (d+1) (bindOneAt L b d p))
  = bindOneAt L b (d+1) (bindOneAt L a d p).
```

The induction generalizes the internal labels and depth; All/Ex use the same
identity at the incremented depth. It is not an external finite-arity argument.
The distinct-label premise is necessary: if `a=b` and the original term is free
`a`, both binding orders choose slot `d`, whereas swapping changes it to `d+1`.

The second checkpoint, `ModelCodedTwoQuantifierSwap`, supplies the finite target
logical proof

```text
T ⊢! (∀∀p) → ∀∀(p.subst [#1,#0])
```

for arbitrary internal typed binary matrices and arbitrary internal theories.
Its two generalizations preserve the actual twice-shifted assumptions. A typed
vector-to-raw substitution lemma identifies its slot exchange with `swapVec 0`.

The numerical client identifies nested named universals with the corresponding
twice-bound body. For distinct labels it applies the first two checkpoints; for
equal labels it uses implication identity. It then applies the actual numerical
`wal` decoder equations and the already checked total decoded implication
congruence, rather than assuming a syntactic homomorphism at numerical zero.
Thus the final numerical theorem has no label inequality premise.

The explicit Lean4.32.0 checks used one thread and a 4GiB compiler limit, with
no dependency builds or downloads. Their focused audits report only `propext`,
`Classical.choice`, and `Quot.sound`:

| Checkpoint | Axiom reports / callers | Recorded source / audit seconds | Warnings |
|---|---:|---:|---:|
| BindOneSwap, first pass | 6 / 8 | 8.686 / 2.003 | 0 |
| TwoQuantifierSwap, pass after one failure | 3 / 4 | 2.559 / 1.953 | 1 unused simp argument |
| DecoderRho4, pass after two failures | 5 / 8 | 2.027 / 1.965 | 3 unnecessary `simpa` suggestions |

The single Template failure was elaboration of composed context maps and an
output arity erased by `.val`; the final source unfolds function composition
and annotates the two-slot vector. The two numerical failures were normalization
of `0+1+1` to the typed arity2 numeral. The successful sources remain byte-exact;
all failed records and source/audit/guard snapshots are retained in the history
record. Historical changed-path hashes are not asserted to match current files.

From a maintained checkout, the three portable guards run sequentially:

```bash
python Logic/Interpretability/ZFCinPA/check_model_coded_bind_one_swap.py --output /tmp/bind-one-swap-replay
python Logic/Interpretability/ZFCinPA/check_model_coded_two_quantifier_swap.py --output /tmp/two-quantifier-swap-replay
python Logic/Interpretability/ZFCinPA/check_model_coded_decoder_rho4_254.py --output /tmp/decoded-rho4-replay
```

Each accepts `--repo`, `--dependency-root`, `--lean`, repeated `--library-path`,
`--source`, `--audit`, and `--prepare-only`. Parent evidence/source/audit and
namespace-cache paths can also be supplied. For relocated selected project
objects use `--bind-one-cache` for the first guard, `--swap-cache` for the second,
and `--project-cache` for the numerical client. These options relocate selected
objects; the numerical parent's explicitly recorded unused Cantor object is a
separate historical input whose exact bytes remain checked. A relocated parent
record may give its new path while retaining the recorded identity.

Each guard checks the exact imported project closure, source/object identities,
actual first external/toolchain providers including Omega, compiler identity,
pins/manifest, ordered audit reports and caller count, then rechecks inputs and
fresh objects. The numerical guard merges the actual Template and rho2 PASS
records and carries the previously accepted, exact same-source Cantor pair;
it does not allow arbitrary object variation. Its selected closure has38 project
predecessors, six external boundaries, and102 recorded input paths.

The packaging controls comprise six genuine unbuilt portable/relocated
preparations and nine rejected wrong-source, existing-output, or optimized-Python
invocations. Preflights query the compiler version but perform zero Lean proof
builds. They are distinguished from the three actual successful kernel checks.
