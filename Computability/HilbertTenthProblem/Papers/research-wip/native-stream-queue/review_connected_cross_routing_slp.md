# Independent review of the complete connected routing SLP

**PASS after the source-bytecode authentication repair. No unresolved mathematical, source-counting or public-interface finding.**

Reviewed `/tmp/connected_cross_routing_slp.py` at SHA-256 `91aa4fedbf1251baa2b385065f97dbe79c59cbce04244839c753558b55c67a4e`, its full companion note at `c2e14297ee1c1a8b42d25b12417e5df2084948efb6c30fe1d750e5fd94d8326b`, and the complete pinned parent `substrate.py` at `3dd949eae682c7b57d2c3ee9f8e86dad5d40c156a33d6010568868bc1b9173e4`. The independent checker accepts explicit helper/source paths and pins both before execution. It edits no production source or archive.

## Complete identity and scope

At each external time, the parent routing contribution is `C=Σ_(r≠s,j)b_s a_rj`. Independently distributing products proves

`C=Σ_j(B A_j−Σ_r b_r a_rj)=B Σ_j A_j−Σ_r b_r A*_r=Σ_r(B−b_r)A*_r`,

where `B=Σ_r b_r`, `A_j=Σ_r a_rj`, `A*_r=Σ_j a_rj`. This is an equality in the polynomial ring. It uses neither B=1 nor a routing equation nor a nonnegativity assumption. The source handles R=0 and R=1 by the literal zero cross polynomial. Every original affine residual and its multiplicity is retained; structural reuse of a squared register does not remove repeated occurrences from the final sum.

I independently reconstructed the **entire** parent certificate from program descriptors: initial counters/control/history, all branch and transition equations, one-hot selectors, zero/positive branch guards, history recurrence, endpoint HALT, the tridiagonal electrical equations, charge, terminal voltage and every direct cross occurrence. This reconstruction does not call the parent's compiler, energy evaluator, expansion routine or the author's symbolic checker. Expanding every emitted gate agrees exactly with the resulting complete quadratic polynomial. Each affine residual register was separately compared.

Therefore all four complete output polynomials agree on arbitrary integer tuples. The parent's complete natural zero theorem, coordinate list, parameters and canonical fibers transfer verbatim. Signed internal subtraction is allowed; signed **witness** zero semantics are not thereby proved. The horizon T remains external, and the provided programs are finite examples/stress fixtures rather than a fixed universal machine instance. The accepted m=3 case is a finite recurrence-polynomial option; the connected infinite-network/coercivity interpretation requires m≥5. The note states both qualifications correctly.

The degree is exactly two uniformly: no gate exceeds degree two, and each input parameter x_j occurs in an input-binding residual whose square gives coefficient +1 on x_j²; no other term cancels it.

## Paid arithmetic

Every emitted binary addition, subtraction and multiplication is charged once; nonunit scalar multiplication is an emitted multiplication. Zero/one identities and fixed-constant folding are valid at no input-operation cost. The selector sum and routed-column sums are charged in every mode and reused by the actual residual registers; they are not counted as free external inputs. The row sums needed by the factored routing modes are also emitted and paid.

I independently counted every gate and checked that every gate lies in the dependency closure of the complete output. All references are acyclic and typed, names are unique, and no duplicate structural operation survives the claimed CSE. The final accumulation and the addition of the routing term to the sum of residual squares are included. Thus the selected totals in the companion note refer to complete evaluators, not only a favorable routing fragment.

The routing-only difference formulas in the note follow directly from these explicit schedules. In particular the row-diagonal formula saves `T(d−1)(R+1)` multiplications relative to column-diagonal routing while preserving the addition count. For R≥4, row-complement saves T multiplications and costs `T(R−d)` extra additions relative to row-diagonal. The note correctly avoids claiming that any one mode always wins; R=2 and R=3 have additional literal subset/wire reuse.

The complete reported examples were included in the independent reconstruction: transfer at T=3 is 245 direct versus 206 row-complement; the five-branch d=3,T=4 fixture is 840 direct versus 456 row-diagonal; the eight-branch d=2,T=3 and four-branch d=6,T=3 totals also match. These figures do not establish a new fixed-arity universal-equation operation bound.

## Independent tests and repaired finding

The deterministic checker covers 164 complete source forms, 4,432 literal affine residual comparisons, 29,802 live paid gates, 164 complete symbolic polynomial identities, 328 full manual numeric evaluations including signed tuples, 29 malformed-packet/domain rejections and two defensive-copy checks. It covers T=0, zero/one/two/many branches, d=1 through d=6, nonzero initial control, m=3 and m=5, and all displayed stress schedules. Writer and fresh saved-receipt replay both passed.

The first source loader used `SourceFileLoader.exec_module` after hashing only the `.py` file. A cold matching timestamp/size forged `.pyc` therefore executed different code despite the correct source hash. `/tmp/repro_connected_bytecode_pin.py` reproduced this directly. The final source hashes the bytes it executes and calls `exec(compile(data,path,'exec'),module.__dict__)`; the independent check constructs the same forged bytecode cache and confirms that the authenticated full packet is emitted. The warm-cache source guard remains in place. This repair changes authentication only, not the polynomial or ledger.

## Replay

```sh
python review_connected_cross_routing_slp.py \
  --helper /path/to/connected_cross_routing_slp.py \
  --source /path/to/well_conditioned_diophantine/src/substrate.py
```

The default compares with `review_connected_cross_routing_slp.json`; `--write` explicitly regenerates that receipt. This bounded audit does not rerun the already-reviewed full connected-network author suite or establish new analytic theorems about the infinite operator. It verifies the concrete complete arithmetic rewrite and its stated inherited scope.
