# Shared natural registers before quartic compilation

`NaturalRegisterProgram.lean` adds executable program data that preserve shared
arithmetic registers before constructing an expression tree. A program stores
a finite arithmetic DAG. Its topology and nonnegativity certificates are proof
fields about that supplied data.

Each `Program.push` appends exactly one operation: a natural literal, an input,
an addition, or a multiplication. Operands of a binary operation have type
`Fin p.nodes.length`, so they refer to the existing register bank. A later
operation can use one earlier register multiple times without duplicating the
computation that produced it. The constructor itself proves topology and
nonnegativity; it requires no external compiler-correctness assumption.

The checked interfaces are:

- `Program.old` and `eval_old`: preserve every existing register and its value;
- `Program.last` and `eval_last`: identify the new register with the supplied
  local operation's value;
- `Program.Realizes` with literal/input/add/mul closure theorems: attach a
  semantic specification to a register while retaining the program data;
- `Program.equalityRep`: compile equality of two selected output registers to
  an ordinary `Rep` using `NaturalDAGQuartic`.

For a program with `n` inputs and `m` registers, the final representation has
exactly `m` natural gate witnesses, hence `n+m` natural variables including its
inputs. Its polynomial has degree at most four, and its integer expression
has at most `6*m+4` binary operations. The proof covers every natural input;
canonical nonnegative circuit values supply the gate witnesses. The expression
is constructed only at this final boundary. No polynomial data are extracted
from a proposition or chosen using `Classical.choose`.

`checks/NaturalRegisterProgram.lean` builds a four-register program computing
`x`, `y`, `x*x`, and `(x*x)+(x*x)`. The last operation reads the same square
register twice. Its universal correctness theorem states that the resulting
four-witness quartic has a natural solution precisely when
`x*x+x*x=y`. This example checks sharing and the representation interface; it
is not a claim that a quartic is the smallest encoding of that simple graph.
The nine dependency audits use only `propext`, `Classical.choice`, and
`Quot.sound`, sometimes a subset.

This foundation handles equality of polynomial circuit outputs. A graph
compiler for the proof checker or enumerator now also has explicit
[existential scopes and pairing graphs](SHARED_REGISTER_RELATIONS.md).
Relational composition, guarded arithmetic and the bounded quantifier
construction remain to be integrated. No smaller closed consistency equation or internal
object-ZFC biconditional follows from this module alone. The existing closed
direct quartic and its independently checked conservative size bound remain
in `DirectQuarticZFC.lean` and `DirectQuarticSize.lean`.
