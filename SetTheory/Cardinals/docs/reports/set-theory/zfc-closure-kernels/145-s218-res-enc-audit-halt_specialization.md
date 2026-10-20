# Specializing the only halting equality test

This is a source-equivalence theorem, with a fresh finite inductive certificate. The source-size result alone does not assert a smaller compiled Turing machine.

## Exact context and invariant

The original K219 subtree at binary prefix `1110100101` is

```
(CI6, ((E, CH), tail))
```

where `E` is the pinned K219 equality macro on registers 5 and 6. Its first twelve leaves occupy zero-based ordinals `[4598,4610)`. The complete guarded CFG has exactly one external entry into this interval, `39 -> 4598`, and one ordinary outgoing edge, `4608 -> 4610`. The remaining terminal possibility is `CH` at ordinal 4609.

The fresh pointwise zero/positive abstract interpretation proves, at ordinal 4598,

```
R0 positive; R1,R2 arbitrary; R3=0; R4,R5 arbitrary; R6=R7=0; R8 arbitrary.
```

Each register uses only the two abstract atoms zero and positive. The analysis processes 19,814 work items; a separate pass verifies seed inclusion and all 6,163 admitted abstract edges. Thus this is an induction for arbitrary natural registers, not a finite execution trace or a finite register-value test. Its correctness follows from soundness of the increment and guarded-decrement transfer rules and induction on execution length.

Writing `D5=CD5`, `D6=CD6`, `B=CB1`, `C1=CC1`, `C2=CC2`, the exact equality macro is

```
U = ((D6,C2),B)
E = (((D5,U),D6),((D5,C1),U))
```

Its existing unbounded contract is: clear registers 5 and 6; return normally when their entry values are equal; otherwise exit by `CB1`. The proof uses only loops that decrease a natural register and has no upper bound on its inputs. The old initial `CI6` changes the proved-zero register 6 to one, so the old test halts exactly when the entry value of register 5 is one. Otherwise it exits to `tail` with both tested registers zero.

## Replacement that reuses the equality macro

Let

```
H = (D5,(E,CH)).
```

Replace the displayed old subtree by `(H,tail)`. At the unique entry, write the value of register 5 as `n` and use the proved fact `R6=0`.

- If `n=0`, the first `D5` takes its zero branch, which exits `H` normally. Registers 5 and 6 remain zero.
- If `n=1`, the first `D5` leaves zero in register 5. Now `E` compares zero with zero, returns normally, and executes `CH`.
- If `n>=2`, the first `D5` leaves the positive value `n-1`. Now `E` compares that value with zero, clears both tested registers, and takes `CB1`, skipping `CH` and returning normally from `H`.

Every other register is untouched by the test. This is exactly the old test's contract under its proved entry invariant. The replacement retains 206 DAG nodes and 4,744 leaves. It changes primitive contexts and adds a decrement guard, so it still requires fresh compilation/runtime validation.

The candidate also has a fresh pointwise inductive proof: 19,783 work items and 6,159 admitted abstract edges. In particular, all three `CD6` occurrences at ordinals 4600, 4603, and 4606 have zero input. Ordinals 4601 and 4607 are unreachable.

## Compilation status

A raw incremental 219-state compilation of the reuse-E source was rejected. It changed the protected arithmetic row 38/0 from `0R13` to `0R303`. An all-zero-register CI5 interface at PC `111010010010011110` reaches that row and fails. A separate screen of 876 single-row repairs found no passing repair. The source-equivalence theorem therefore does not certify that rejected table: preserving all shared arithmetic roles or proving new complete interfaces remains a necessary compilation obligation.

## Two direct six-leaf versions

The same contract is implemented by either of these macros:

```
S  = ((D5,((D5,B),CH)),(D5,C1))
S2 = (D5,((D5,((D5,C1),B)),CH))
```

For `S`, entry value zero skips the conditional and passes through the zero clear loop; entry value one makes the second decrement zero and reaches `CH`; a value at least two passes through both positive decrements, then `B` skips `CH`, and the clear loop removes the remaining `n-2` units. The clear loop terminates because each repetition decreases register 5. Register 6 remains zero throughout.

For `S2`, the first zero decrement exits the whole macro; after a positive first decrement, the second zero decrement reaches `CH`; after two positive decrements the clear loop runs and `B` skips `CH`. Again, the clear loop decreases a natural number and terminates. These two macros each have six primitive leaves. Replacing the old context by `(S,tail)` or `(S2,tail)` produces 4,738 leaves but 208 DAG nodes: the shorter primitive word does not automatically improve the sharing metric.

## Whole-source transport

The verifier checks both pinned CFG constructions and all 6,150 guarded edges outside the changed interval. Each outside primitive keeps its effect; every outside successor is mapped exactly by the index shift. The only entry remains ordinal 4598, and every ordinary macro exit reaches the corresponding first instruction of `tail`. Each replacement macro has boundary `(0,0,True)`: no escaping break or continue, and a halting branch.

Relate old and new executions at corresponding outside ordinals and at the macro entry. The finite macro analysis above either matches a halt or returns with identical registers. Consequently the old inductive invariant continues to justify every related macro entry; the candidate's fresh invariant supplies an independent check. No new divergence can occur inside the macro, because all of its nontrivial loops strictly decrease a natural register. This gives equivalence of halting from the initial seed in both directions.

The receipts and executable checks are ordinary finite induction certificates, not proof-assistant kernel certificates. The local, unbounded macro arguments are the mathematical three-case proofs above.

## Replay

After extracting the pinned dependencies using the packet's main replay command and setting `PROVEIT_K221_PORTABLE` as in `README.md`:

```
python research/encoding/audit/scripts/verify_halt_specialization.py --variant reuse_e --out /tmp/halt-reuse-proof
python research/encoding/audit/scripts/verify_halt_specialization.py --variant six_leaf --out /tmp/halt-six-proof
python research/encoding/audit/scripts/verify_halt_specialization.py --variant six_leaf2 --out /tmp/halt-six2-proof
```

Each command reconstructs its exact source, recomputes both inductive invariants, checks the context, and emits a receipt. The optional `--candidate PATH` additionally checks byte-decoded equality with a separately supplied source file.
