# Closed source macros and semantic rewrites

Let `Move(a,b)` repeatedly decrement a and increment b until a is zero, with
the two registers distinct. It is a closed structured command: it returns
normally, has no halt, and has no outward break or continuation. On natural
input values `(a,b)=(x,y)`, after k iterations, for 0≤k≤x, its values are
`(x-k,y+k)`. Hence it terminates after x iterations and returns `(0,y+x)`.

## Increment transport

For every natural x,y,

\[
\operatorname{Move}(a,b);\operatorname{Inc}(b)
\quad\equiv\quad
\operatorname{Inc}(a);\operatorname{Move}(a,b).
\]

The left side reaches `(0,y+x)` and then `(0,y+x+1)`. The right side reaches
`(x+1,y)` and then `(0,y+x+1)`. Both terminate, and all other registers are
unchanged. No zero-register precondition is required. This statement is
an elementary identity, not a claim of a new mathematical theorem.

Replacing a closed source region by another region with this exact
termination and register-transform property preserves the source program's
halting behavior. Collapse each execution of the region to one macro step.
The original and rewritten programs have identical boundary configurations.
Every expanded macro takes a finite positive number of primitive steps and
has no halt. Finite halting traces therefore correspond. An infinite trace
cannot become stuck forever inside a single such macro; conversely,
infinitely many macro boundaries expand to unbounded primitive time.

For routing245, set `a=X`, `b=H`, and use symbols
`g=Move(X,H)`, `m=Inc(H)`, `h=Inc(X)`. The sound replacement is `gm → hg`.
It changes four expanded regions. Their current routed prefixes are:

1. `11101001001011000011`
2. `1110100100101110011`
3. `1110100101100011`
4. `111110011`

The literal table changes only:

| Row | Old action | New action |
| --- | --- | --- |
| `(142,0)` | `(write 0, R, 37)` | `(write 0, R, 39)` |
| `(142,1)` | `(write 1, R, 72)` | `(write 1, R, 37)` |

The original-label roles 37, 39, 72 decode g, h, m respectively. The 245-state
table, exact blank trace, and conditional universal prefix audit are
retained under `results/hg-swap/`. The 300-second grammar search did not find
a 127-rule grammar.

## Why deletion is different

The physically smaller edit removes state 142 and redirects its unique
external incoming transition to the `m` decoder. Unique physical entry does
not imply unique semantic occurrence: the decoder is shared. The edit
replaces all four occurrences of `gm` by `m`.

In the destructive equality test, if input x exceeds input h, the comparison
has already consumed h paired decrements and one further decrement of X
before entering g. Thus g clears the residual `max(x-h-1,0)`. Deleting g leaves
that value in X. The final inequality branch is selected correctly, but the
register transformation is no longer the same.

The next parameter copy adds into X. An independent exact source replay in
the enclosing archive starts a two-gate region at
`(N,T,W,A,D,H,X,Y,L)=(3,7,0,2,2,0,0,0,0)`. The original clears T in 58 steps;
the pruned source retains T=7 after 41 steps at the same exit, with the other
registers agreeing. This refutes the proposed contextual macro equivalence.
It does not by itself establish a theorem about the eventual halting of the
pruned binary machine from blank.

## A weaker tape representation relation

An instruction simulation need not preserve physically unused spare blocks
or absolute coordinates. A sufficient relation is: every binary frame
encodes the correct source pointer and nine primary registers, together
with a valid positive finite spare suffix and an adequate gap. Every
nonhalting source instruction must lead in a finite positive number of
binary steps to some frame for its exact successor; halting instructions
must lead to binary halt. The relation is universally quantified over all
frames in its domain.

Induction concatenates finite segments for finite source runs. An infinite
source run yields infinitely many positive-length binary segments; by
determinism these form the actual binary run. A separate finite blank
bootstrap must place the machine in a frame belonging to the source
theorem's initial domain. This is the familiar compositional simulation
argument. The weak and frame mutation screens test finite instances of
such relations. Their failure does not disprove the usefulness of the
general relation, and their finite gap 181 choice is not a universal gap 64
certificate.
