# Independent audit of the fully emitted unbounded clean-clock circuits

**PASS within the stated fixed-source, natural-input scope.** All ten JSON circuits and all eight accompanying textual DAGs pass an independent data-only check. The checker does not import or execute the emitter, any Python under `source`, or the upstream author's verification code. It authenticates the upstream JSON receipt against SHA-256 `fe69f0504c8f68c4130c4b21fed5c817596ab5c0e2fdf9621b0bf5f45c12ac0e` and treats its arithmetic gate lists as data.

The independently checked files are recorded by hash in [the machine-readable audit receipt](independent_emitted_circuit_audit.json). The independently written [checker](check_emitted_circuits.py) verifies the emission manifest but does not trust the emitter's ledger or degree certificate without recomputing them. A fresh process reproduced the audit receipt byte-for-byte.

## Full counts, without an unpaid finalizer

| Fixed source | Native M | Native A | Native total | Positive witnesses | Exact degree | Phase4 total |
|---|---:|---:|---:|---:|---:|---:|
| INC2;DEC2 | 239 | 365 | 604 | 60 | 2344 | 605 |
| Prime-three zero test | 184 | 295 | 479 | 58 | 1192 | 480 |
| Nop | 182 | 295 | 477 | 58 | 1192 | 478 |
| Prime-three positive test | 189 | 291 | 480 | 58 | 1192 | 481 |

Each circuit has precisely two natural parameters, `x` and `Tclean`. Each phase4 circuit adds exactly one multiplication by the literal integer 4, with the same addition count, witness count, and degree as its native circuit. A spatial block relabeling is represented by the same native-clock circuit, conditional on the established graph correspondence; this arithmetic audit does not introduce an extra spatial scaling assumption.

Every complete nonempty-history circuit has twenty comparisons and a complete 59-gate SOS finalizer: twenty subtractions, twenty squarings, and nineteen additions. Every comparison is represented exactly once. The output is the final sum of all twenty squares, not an intermediate residual or a partial sum.

The finalizer cost does not increase relative to the raw circuit: the former endpoint row is replaced by the clean-time row. Thus the native net increment is exactly the six clock-bridge gates, 2M+4A. It would be incorrect to charge an additional comparison while also counting the removed `F=y` comparison as retained.

## Exact inheritance and endpoint elimination

The raw core contains 539, 414, 412, and 415 gates respectively. Each is reproduced literally, in order, with the sole operand substitution `T -> theta_positive`. The checker verifies 3,560 such identities across the eight nonempty-history circuits. No source-machine table, map, or other raw arithmetic gate is changed.

The raw equality `final_positive = y` is the twentieth comparison. The only occurrence of the exact input coordinate `y` as a gate operand is the right operand of `sos_res19`; it does not occur in the raw core or any other comparison. The similarly named native auxiliary `native__y_aux` is a different coordinate and is retained. All nineteen remaining raw comparison pairs are kept verbatim under the same clock substitution, including every native guard and the paid raw clock equation. This is checked as 152 comparison-pair identities across the eight circuits.

The emitted positive witness list is exactly the raw positive witness list followed by `theta_positive`. There is no new endpoint witness: `final_positive` was already a raw positive coordinate. Neither old external input `y` nor old external clock parameter `T` remains as an undeclared or hidden port.

Writing the nineteen retained residuals as `E_i(x,F,theta,w)`, the complete clean polynomial is exactly

    sum_i E_i(x,F,theta,w)^2
      + (192*(F+x+1) + 2*theta + 16 - Tclean)^2.

Over the integers, this is zero if and only if all nineteen retained equations and the new time equation hold. Existentially taking `y=F` restores the deleted raw endpoint row. Conversely, any satisfying raw tuple at `y=F` yields a satisfying clean tuple at the displayed clean time. Making `theta` strictly positive loses no accepted run in these fixtures: their initial and halt states are distinct, and the inherited raw theorem describes nonempty first-halting runs with strictly positive ticks. This last semantic assertion depends on that theorem, not on random arithmetic evaluations.

## Clean-time and phase4 identities

The added six-gate bridge is expanded independently as an exact integer affine form. In every native circuit it equals

    192*F + 192*x + 2*theta + 208
      = 192*(F+x+1) + 2*theta + 16.

The constant 208 includes the 192 coming from `x+1`; it is not a replacement of the final `+16` by `+208`. The phase4 bridge is exactly four times the entire native affine form, including the constant. Its prefix is identical to the full native pre-finalizer DAG and its only new gate is multiplication of `clean_native_time` by 4.

Two initially halted cases are emitted separately. Substituting `F=x+1` and `theta=0` gives

    native: Tclean = 384*x + 400,
    phase4: Tclean = 1536*x + 1600.

Each is implemented with four gates, 2M+2A, one comparison, no positive witnesses, and exact degree 2. The phase4 constants are folded into the same four-gate schedule. They are not represented as nonempty residue histories. For each model, all `x=0,...,100` were evaluated at the required time and at the two adjacent times; the respective polynomial outputs were exactly 0 and 1.

## Closure, liveness, and algebraic checks

The checker requires distinct declared ports, fresh named gates, exactly one allowed operation per row, integer literal constants, and each operand to be either an earlier gate or a declared port. Boolean JSON values are not accepted as integers. The complete ancestor set of the output is exactly the set of all declared gates and ports. Therefore there are no dead listed gates or coordinates, forward references, undeclared registers, or hidden oracle/exponentiation operations. The literal-constant sets are independently extracted and compared with the emitted ledgers. This verifies the stated arithmetic model with literal integer constants; it is not a claim that those constants are synthesized for free in a different cost model.

The textual DAGs parse back to precisely the corresponding JSON gate lists, input declarations, and outputs. The emission manifest's eighteen file hashes and all its ledgers agree with the actual files and independently recomputed results.

In total, 4,092 emitted arithmetic gates and 162 SOS rows were audited. The structural finalizer check proves the displayed SOS identity formally. As independent finite sanity checks, the full DAGs were evaluated at 120 signed integer assignments and 320 assignments modulo 1,000,003, then compared with direct evaluation of the sum of squared comparison differences. Integer nonnegativity and integer zero equivalence were checked for the signed trials. No modular zero equivalence is inferred: over a finite field, a sum of squares can vanish without each summand vanishing.

Eight deliberately corrupted circuit copies were also rejected: an omitted witness, an undeclared operand, a changed inherited gate, a deleted retained comparison, an altered clean-time constant, an extra dead gate, an undercounted ledger, and a false degree claim. These are checker regression tests, not modifications to the emitted artifacts.

## Independent exact-degree certificates

These are exact degrees of the emitted integer polynomials, strengthening the upstream raw note's upper-bound-only claims for the present clean outputs. They are not lower bounds on arithmetic circuit size and do not assert minimality of the paid schedules.

Assign every declared coordinate formal degree 1 and every integer literal degree 0. At a multiplication use the sum of the operand bounds; at an addition or subtraction use their maximum. At every gate, also propagate the homogeneous component at exactly that formal bound, evaluated modulo `p=1000003` after substituting coordinate `i` by `(i+2)*z`, with `i=0,...` in the emitted order `parameters + auxiliaries`.

For a gate with bound `D`, lower-bound operands contribute zero to the degree-`D` component of a sum or difference. Products multiply the components at the two operand bounds. Crucially, a zero evaluated component never lowers any formal degree bound. The checker retains the degree bound even when the chosen weights cancel its top component. Each nonempty circuit contains two such zero-top trace entries; an additional explicit cancellation regression checks that this rule remains in force through later products and sums.

Induction on gates gives both an upper bound on total degree and the evaluation of the true degree-`D` homogeneous component at that bound. If the output component is nonzero modulo `p`, the integer homogeneous component is not the zero polynomial. Therefore the output has degree at least `D`, establishing equality with the upper bound.

| Emitted family | Formal degree D | Output top component mod 1000003 |
|---|---:|---:|
| INC2;DEC2, native and phase4 | 2344 | 135347 |
| Zero test, nop, positive test, native and phase4 | 1192 | 977370 |
| Initially halted, native | 2 | 585225 |
| Initially halted, phase4 | 2 | 418734 |

Every output value is nonzero. Every gate's full `(name, formal bound, evaluated top component)` trace, every substitution weight, and every other supplied certificate field matches the independent recomputation. The equal native/phase4 top values are consistent with scaling only a degree-one time residual while the other retained constraints supply the much higher output degree.

## Scope and reproducibility

The audit establishes exact emitted-source inheritance, paid arithmetic counts, complete SOS identities, bridge identities, closure, liveness, and exact degrees. The interpretation as cleaned three-mass first-halting reachability remains conditional on the authenticated raw residue-history/native theorem and the established cleanup/unique-reverse-lift theorem. This audit does not independently reconstruct the full historical Pell theorem or a spatial/physical realization proof.

No complete positive native Pell witness tuple has been numerically materialized. Signed and modular algebraic test assignments are not claimed to be satisfying positive native witnesses. The artifacts remain four fixed nonuniversal sources with no horizon parameter. They establish no ordinary-input universal loader, new universal operation bound, or optimality result.

Reproduce in a standard-library Python process:

    python audit/check_emitted_circuits.py \
      --expect audit/independent_emitted_circuit_audit.json

Run that command from the artifact root, or use the script's absolute path together with an absolute receipt path. The script locates its artifact root from its own path by default. Omit `--expect` to regenerate only its audit receipt. No repository source or Git state is read or changed by this checker.
