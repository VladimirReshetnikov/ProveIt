# Independent certificate and command-interface audit

## Scope and actual result

This audit uses a separately implemented reader rather than rerunning the
same generator's validator. It was authored and run in the present session.
It checks the supplied finite symbolic certificate and reviews the ordinary
all-natural scheduler proof. It is not a Lean/Rocq kernel check or a binary
machine certificate.

The command

    python3 -B independent_ordered_audit.py

passes and writes `independent_ordered_audit.json`. The reader imports only
Python's standard library: it neither imports nor executes
`ordered_commutation.py` or the inherited `hilbert.py`.

## Exact certificate checks

The file `ordered_commutation_dag.json` has 600 nodes. Every node is checked
for its permitted schema, exact formula, earlier parent indices, and exact
open-hypothesis set. MP requires literal antecedent equality. GEN requires
one closed premise and produces exactly the stated quantifier constructor.
A hypothesis node is assigned precisely its own open-hypothesis ID.

The complete stored graph contains:

| Rule | Count |
|---|---:|
| K | 122 |
| S | 99 |
| Double-negation elimination | 4 |
| rho2 | 5 |
| rho6 | 5 |
| Oriented rho4 | 1 |
| Generalization | 5 |
| Modus ponens | 323 |
| Temporary hypothesis scaffolding | 36 |

The two closed output nodes have a 488-node dependency graph. It contains
all the listed axiom/GEN nodes and 247 MP nodes, but **no hypothesis nodes**.
Thus the 36 hypothesis nodes in the stored construction history are not
undischarged assumptions in either theorem.

The sole oriented-rho4 axiom is node70. Its labels are literally the
parameters `(a,b)`, and its matrix is
`not(Box_b(Box_a(x)))`. The independent schema reader rejects any such
axiom whose labels differ from that exact orientation. The reverse
orientation appears only as the required derived output. No opposite
orientation is smuggled in via an auxiliary axiom name: the reader permits
only K, S, DNE, rho2, rho6, oriented-rho4, MP, GEN, and hypothesis nodes.

All five GEN premises have empty hypothesis sets. The final two formulas
are checked against independently constructed ASTs:

    Box_b(Box_a(x)) -> Box_a(Box_b(x)),
    x -> Box_a(Diamond_a(x)).

## Mathematical assumptions outside this finite audit

1. K, S, and classical double-negation elimination are available for every
   native natural-code instance from the inherited dominated-rho8 result.
   This audit does not execute that separate larger derivation.
2. rho2, rho6, numerical MP, and theorem-only GEN have their stated native
   code definitions and are retained in the restricted calculus.
3. The compositional native constructors turn syntactically equal ASTs
   into equal numerical codes. Constructor injectivity is not assumed.
4. A fixed natural assignment to schematic parameters evaluates every
   checked axiom instance and inference. This is a metatheoretic family
   of finite numerical proofs, not an object-language substitution rule.

The native zero alias I(0,0)=0 is compatible with all four assumptions.
The proof never argues from unequal ASTs to unequal native codes.

## Exact file identities

| File | SHA-256 |
|---|---|
| `ordered_commutation.py` | `33716f21c30906215f5ca36d791c8b02a66061033c3a30158bcb8cd6735fe350` |
| `hilbert.py` | `63396d6ec0b98744b8b4502c316fbdb7fdb018dcda1dbaed0d2e612e5351b7cc` |
| `ordered_commutation_dag.json` | `a9167755d1b6b17f6103af9831a483713475de04f1600a77eb38b074862cb3cc` |

The independent reader and its result are `independent_ordered_audit.py`
and `independent_ordered_audit.json`. The include-ready exposition is
`ordered_commutation_section.tex`. These paths are relative to the
calculus contribution directory.

## Scheduler proof and the two transfer commands

`permuted_credit.md` now explicitly applies to either implementation:

- Single-guard S: halt if cache h=1; otherwise return (h,w,d,z) from
  (t,[z;w],d,h). Clear-top, copy-cache-to-top while preserving cache, then
  old-NIP implements this map when its source contracts are checked.
- Composite S': halt if h=1 or t=1; otherwise the same return map.
  Old-DROP; old-NIP; old-NIP implements it. Its two guard tests occur on
  old cache and saved old top, respectively.

Both consume exactly one preexisting stack head on a normal return and
consume no payload field beyond selector1. The credit recurrence depends
only on that common effect. Its one-head credit at cutoff1 and ten-head
startup margin9 therefore apply to either command. Soundness accounts
for exactly the guard or guards of the chosen implementation. The
single-guard strong compiler applies directly to S, while replacing S by
S' is an early-halt refinement and preserves every strong
"halts-or-returns" contract.

The own standard-library checker `permuted_credit_check.py` corroborates
500000 candidate summaries,1000 explicitly expanded words, and997 complete
diagonals. `permuted_credit_result.json` is the actual record. The universal
result comes from the finite-descending recursion and diagonal proof in
the Markdown note, not from extrapolating those finite checks.

The 68442-step binary startup and174-primitive AX-prefix match in that
note are separately measured premises for the earlier matched composite
candidate. A newly allocated shorter single-guard source must have its
own literal source and startup evidence; this audit does not transfer
those measurements automatically.

## Explicit limitations

No state saving is proved by ordered rho4 alone. No globally ordered AX
parameter scheme is calibrated. No new binary transition table, arbitrary-
value binary simulation, blank initialization, or proof-assistant endpoint
is certified by this contribution. Those obligations belong to the
candidate's separate source, runtime, and startup checks.
