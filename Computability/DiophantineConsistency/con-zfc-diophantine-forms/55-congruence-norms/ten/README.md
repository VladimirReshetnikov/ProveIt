# Ten unrestricted integers, two-root congruence finalizer

The fixed polynomial in `generated/signed10_b2.json` has **10 unrestricted
integer variables, exact degree 9,152,284, and 586 live binary operations**.
Its lack of integer solutions is provably equivalent in ZFC to Con(ZFC),
composing the new reduction in `PROOF.md` with the pinned ProveIt parent
theorem and the explicitly cited Sun bridge.

The main gain is replacing a norm with three square-root inputs and large
separating weights by an unweighted norm with two square-root inputs. A new
coprime product and Pell guard combine three of the previous requirements;
unconditional congruences rule out cancellation of the two remaining roots.
The displayed equation itself contains only integer polynomial operations.

Against the strongest incoming selective ten-integer form at the audited
snapshot, the degree falls from 21,111,400 to 9,152,284 (56.65 percent) and the
gate count from 659 to 586 (11.08 percent). The number of variables and fixed
coefficient payload are unchanged. No global minimality claim is made.

## Reproduce

Python 3.10 or later is sufficient; no Python dependencies are required.

```sh
python3 build.py
python3 verify.py
python3 evaluate.py --modulus 1000003 0 1 2 3 4 5 6 7 8 9
```

The evaluator's variable order is `f,g,h,k,l,w,x,y,z,m`. Here `f` is the
free parameter called `t` in the proof. The proof's older bridge parameter
is recovered as `2*t+1`; it is not an eleventh variable. The actual bridge
values of `g,h,k` are polynomial expressions in the input coordinates,
specified in the proof and generated DAG.

`verify.py` does not import or execute the builder. It checks all fixed
payload hashes, the 94 literal weighted coefficient recipes, all 49,632
source/pair interactions, and the five failures of the legacy target code.
It checks liveness and operation counts, exact low-degree identities,
independent direct-formula modular evaluations, finite congruence probes,
and nonzero top coefficients proving the exact total degree. The report is
`generated/VERIFIED.json`. These finite checks do not prove the inherited
machine semantics or replace the mathematical soundness/completeness proof.

## File roles

- `PROOF.md`: the full new reduction, hypotheses, degeneracies, and constructive
  completeness of all congruence restrictions.
- `build.py`, `circuit.py`: reproducible division-free arithmetic compiler.
- `generated/signed10_b2.json`: the authoritative literal gate list; the
  retained filename identifies its inherited source adapter, not the old
  finalizer. `schema` identifies the new construction.
- `generated/source_records.json`: every coefficient recipe, not a symbolic
  reference to an unspecified huge integer.
- `code_positive.json`: corrected target assignment for the unshifted source.
- `parameters_shifted_legacy.json`: a documented negative control. It must
  never be substituted for `code_positive.json`.
- `data/`: the exact inherited 31-variable parent and its complete fixed tuple.
- `SOURCE_PINS.json`, `INHERITED_SOURCE.json`, `NOTICE.md`, `licenses/`:
  exact source identity, attribution, and license boundaries.
- `upstream/`: preserved historical proofs. The historical signed10 finalizer
  is replaced by the one proved here.

The containing release supplies a standalone LaTeX/PDF report and the full
source-adapter audit. All register names abbreviate polynomials in the ten
listed coordinates; they are not additional existential witnesses.
