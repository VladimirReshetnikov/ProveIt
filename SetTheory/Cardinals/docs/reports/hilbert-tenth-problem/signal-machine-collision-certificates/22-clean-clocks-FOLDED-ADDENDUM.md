# Literal-constant folding of the complete cleaned-clock circuits

## Result

This separate addendum leaves every file in the previously frozen 44-file base packet unchanged. It emits eight alternative complete circuits, four native/spatial and four phase4, using a five-gate affine clock bridge. The new complete totals for **both** models are:

| Fixed fixture | M | A | Complete operations | Positive witnesses | Exact degree |
|---|---:|---:|---:|---:|---:|
| INC2;DEC2 | 239 | 364 | 603 | 60 | 2344 |
| ZERO3 | 184 | 294 | 478 | 58 | 1192 |
| NOP | 182 | 294 | 476 | 58 | 1192 |
| POSITIVE3 | 189 | 290 | 479 | 58 | 1192 |

Every circuit retains the same two natural ports `x,Tclean`, the same strictly positive witnesses in the same order, all twenty comparison rows and a complete 59-gate SOS finalizer. The source-machine table, native proof dependencies and first-target semantics are unchanged. This is constant folding under the stated literal-integer arithmetic cost model, not a minimality or lower-bound claim.

The original base schedules remain valid and audited: native totals 604/479/477/480 and phase4 totals 605/480/478/481. The addendum saves one addition from each original native schedule and one multiplication plus one addition from each original phase4 schedule. It does not retroactively change the historical emitted ledgers.

## 1. Exact all-tuple polynomial identity

Let F denote the already supplied positive forward terminal payload and θ the already supplied positive native time. The original native bridge computes

`A = 192(F+x+1) + 2θ + 16`.

Expand the fixed constant contribution, obtaining the identity in the integer polynomial ring:

`A = 192(F+x) + 2θ + 208`.

The five paid gates are:

1. `s = F+x`
2. `a = 192*s`
3. `b = 2*θ`
4. `c = a+b`
5. `A = c+208`

This uses exactly 2M+3A. The phase4 bridge originally computes 4A by appending a multiplication by 4. Folding the factor into the fixed literals yields

`4A = 768(F+x) + 8θ + 832`.

Its five gates use the same schedule with coefficients 768, 8, 832. Again the cost is 2M+3A. In particular, the folded phase constant is 832, not 64: the latter would still require the eliminated `+1` inside the payload sum.

The entire pre-bridge arithmetic source is copied literally from the corresponding frozen complete circuit. The final clock output register retains its original name (`clean_native_time` or `clean_phase_time`). Every comparison and every gate in the full SOS finalizer is unchanged. Therefore every residual has exactly the same polynomial value, and the final complete polynomial is identically equal to the corresponding base polynomial on **all integer tuples**, not merely on its constrained zero set. The identity also holds formally over any commutative coefficient ring.

Consequently every domain-restricted zero fiber is literally the same set of supplied-coordinate tuples. There is no witness reparameterization or extra endpoint/time constraint. First-hit semantics, integer-domain restrictions, raw cofactors, no-wrap, infinite positive witness fibers, and all exclusions in the base theorem transfer without another native construction. The no-witness zero-step circuits in the base are already constant-folded and are not changed or duplicated here.

## 2. Complete arithmetic accounting

All fixed scalar multiplications remain paid, as do the residual subtractions, twenty squarings and nineteen finalizer additions. The new bridge costs 2M+3A instead of the original native 2M+4A or original phase4 3M+4A. The complete totals above are recomputed by traversing the actual full DAGs, rather than inferred only from these deltas.

The coordinate list is unchanged, so the positive witness count remains 60/58/58/58. No affine port, large constant multiplication, degree calculation, reverse history, exponentiation or final sum-of-squares construction is hidden from the circuit ledger. Constants are literal integers, as in the base cost model; these operation counts are not constant-synthesis counts in a different model.

Every output ancestor graph is closed and every declared gate and coordinate is live. The deleted gates are the original `F+x+1` addition and, in phase4, the final multiplication by 4. Their effects have been substituted algebraically into the paid remaining gates, not silently ignored.

## 3. Exact degrees

Because the complete polynomials are identical, their exact degrees already follow from the base certificates. The addendum also recomputes the formal-degree/top-component certificate directly on every new gate list. Variables, in emitted `parameters+auxiliaries` order, are substituted by `(i+2)*z` modulo 1,000,003. Formal bounds are retained even when a chosen top component is zero.

Both folded INC2;DEC2 outputs have bound 2344 and nonzero top coefficient 135347. Each other folded output has bound 1192 and coefficient 977370. Nonzero modular coefficients give genuine integer lower bounds matching the propagated upper bounds. Every JSON includes the complete per-gate trace and substitution map. The reported degrees are exact total degrees in all supplied coordinates; they are not lower bounds on the degree or size of every representation of these simple relations.

## 4. Frozen input and reproducibility

The immutable base manifest SHA-256 is

`1bf1225aa950ad1d4f842c8bf098e1935925cd1d52c90453b7696c1321648f95`.

Exact copies of its eight original nonempty circuit JSON files and its manifest are included under `reference/`. Each copied reference is authenticated against its entry in that pinned manifest. Thus the addendum can replay independently of the original absolute workspace path. No upstream or base Python file is imported or executed; the full original arithmetic circuits are read as JSON data.

Run from this directory:

```sh
python emit_folded_clocks.py --check
python audit/check_folded_clocks.py --expect audit/independent_folded_clock_audit.json
python verify_manifest.py
```

The independent audit under `audit/` checks complete polynomial identities, ledgers, domains, closure/liveness, finalizers, degree certificates and numerical all-tuple evaluations without calling this emitter. Its note provides the corresponding replay command. The new `MANIFEST.json` authenticates this addendum separately from the unchanged base.

The data-only audit passes all eight complete circuits and textual DAGs, totaling 4,072 arithmetic gates. It checks the five-gate bridge coefficientwise, reconstructs the unchanged complete SOS, independently computes every full specialized univariate polynomial modulo 1,000,003, and compares 96 signed plus 256 modular complete outputs against the original circuits. Its 22 deliberate corruptions are rejected. The unchanged original base is verified before and after the live-base audit; a second standalone replay authenticates only the self-contained copied references.

The theorem's scope remains four nonuniversal, one/two-step fixture graphs emitted through the generic horizon-free mechanism. No ordinary-input universal loader, optimality result, positive Pell tuple materialization, rational-zero exactness or arbitrary later-recurrence relation is added.
