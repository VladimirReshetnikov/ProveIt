# A concrete proof-carrying command interpreter

[proof_carrying.py](proof_carrying.py) gives an explicit standard-natural-number
construction for the certificate updates described in the
[command-extraction note](../COMMAND-EXTRACTION.md). It uses the existing
checker constructors from the [constructor inventory](../imported-checker/README.md).
It returns a numeric checker certificate if a finite command word halts at
Shift; otherwise it returns 0. This is an executable reference construction,
not an exported PA theorem or a connection from the literal tape machine.

The numeric store and the proof triple are updated by separate functions.
At every nonhalting step, `run_word` checks the live formula certificates and
the entire nonzero numeric-stack prefix. It ignores any proof-stack tail once
the numeric stack is zero, and on underflow it returns the fixed code 739,
which the imported checker accepts as a proof of formula 0. At a halting Shift,
the extractor selects the proof attached to whichever live formula has code 1.
The finite test inputs do not yield a genuine code-1 proof.

The input interface handles **all numeric command atoms**. It follows the
exact [`decodeAtom`](../../../jamesyc-upstream/pa196/PA196/Commands/Coding.lean):
Cantor-decode the atom to `(tag, fields)`; tag 0 is Shift, tag 1 is MP with the
first decoded field, and larger tags give AX with the stored `y` field before
`x`. Unused field tails need not be zero. `extract_hfs_word` accepts a whole
Foundation HFS-coded atom list. This encoding uses Foundation's **square**
pairing plus one for list cells; it is distinct from the source stack's Cantor
pairing. The file implements both explicitly.

## The intended internal statement

Let `F(u)` be the mathematical function implemented by `extract_hfs_word`,
with default output 0 when the HFS word `u` finishes without halting. A precise
command-level target is

```
PA proves: for every HFS word u,
  wordValue(u, stateCode(0,0,0,0)) = 0
  implies Checker.verifyValue(F(u)) = 2.
```

`2` means an accepted native calculus proof of formula code 1. This statement,
if established, would not yet translate that certificate into a PA refutation
or show that an arbitrary literal-machine halt yields such a command word.
It also does not say that PA proves a halt occurs.

A concrete route to this statement is as follows. Encode the finite tuple
consisting of the live command store, the three certificate components, and a
halted flag/witness. Each update is a fixed composition of Cantor pairing and
unpairing, the numeric head expressions, equality tests, and the imported
`leafCertificate`, `mpCertificate`, and `genCertificate` functions. The
halted case retains its witness. Iterate this total update over the HFS list;
the HFS tail is strictly smaller than its nonzero code, so recursion bounded
by the original word code suffices. The other arithmetic functions involved
are primitive recursive, including bounded square root, pairing and unpairing,
and the numeric expression evaluators. PA proves totality of primitive-recursive
functions. The Python code does not itself establish their PA representations.

The induction invariant is a disjunction. In the live case the command store
is an actual four-field `stateCode` and the two live certificates check, while
`Good(w,pw)` holds for the bounded numeric-stack prefix. In the halted case the
command state is 0 and the retained checker certificate checks formula 1.
The three update cases preserve this invariant using the imported all-model
`verify_head*`, `verify_r8`, `verify_bundle`, `verify_mp`, and `verify_gen`
equations, together with the [stack lemma](../README.md). For AX, all head and
bundle expressions ignore the fourth evaluator argument except `rho8`; the
latter receives the actual `d` in both the command and checker expressions.
For noncanonical atoms the first Cantor tag, not atom equality with 0 or 1,
selects the branch. For Shift, `t+h=1` implies `t=1` or `h=1` in PA. The
zero code for a halted *command state* differs from a live HFS store with four
zero fields, whose encoding is nonzero.

To turn this into a checked PA result, one must write the graphs for this
particular total update and iteration, verify they correspond to the imported
all-model command and checker functions, and carry out the full induction in
PA. The imported `CommandWord.prefixGraph` already represents the command
run, and the imported checker has a total unique `verifyGraph`, but this
annotated iteration and its induction have not been implemented. The paragraph
above is a construction and proof outline, not a claim that the displayed PA
sentence has been formally derived here. The proposed extraction of a command
run from a source halt has additional obligations recorded in
[SOURCE-COMMAND-EXTRACTION.md](../SOURCE-COMMAND-EXTRACTION.md).

## Finite controls

From the repository root, with Python 3.10+:

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/reverse-cert-stack/annotated-interpreter/replay.py > /tmp/pa196-annotated.json
```

The output matches [receipt.json](receipt.json). It covers successful MP at
`I(0,0)=0`, failed MP, both AX guard outcomes, nine successive shifts through
the produced head list, an underflow with a nonzero ghost proof stack, malformed
proofs, canonical and noncanonical atoms, square-pair round trips, and several
HFS word executions. Two intentionally invalid stores test only which proof
slot is selected at halt; they are not accepted contradiction certificates.
The checks raise explicit exceptions and reproduce under `python3 -O`. The
checker evaluator is the existing finite Python transcription; agreement on
these examples is not a proof in PA or an independent proof kernel.
