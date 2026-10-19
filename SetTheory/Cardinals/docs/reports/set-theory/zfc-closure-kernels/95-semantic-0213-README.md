# A shared equality cleanup cannot be deleted

This folder contains an exact counterexample to a proposed source justification
for a 244-state mutation. The mutation bypasses grammar state 142, whose word
`gm` means `Move(X,H); Inc(H)`, by changing state 119's transition on `1` to
`1 R 72`. State 72 implements `Inc(H)`.

The important source question is how many times that shared grammar word occurs
in the expanded program. A single incoming physical transition does not imply
a single expanded source occurrence. The verifier reconstructs complete binary
source trees from the two prefix tables and proves that the proposed replacement
deletes **four** copies of `Move(X,H)`. The baseline has 6,460 instruction leaves;
the replacement has 6,448. The four baseline loop entries are at indices 6282,
6301, 6316, and 6426. Only the third had an inherited interval certificate forcing
`X=0` at entry.

## The algebraic error

In the inherited equality macro, repeated simultaneous decrements first cancel
the common part of `X=x` and `H=h`. When `x>h`, the macro reaches its cleanup
branch with `X=x-h-1` and `H=0`. The original `Move(X,H); Inc(H)` clears the
remaining `X` and makes `H` positive. A subsequent decrement, clear, and break
clear `H` and take the unequal branch. When `x=h`, the following conditional
action is executed. When `x<h`, the macro clears the remaining `H` and takes the
unequal branch.

Thus the original macro both tests equality and clears **both** scratch
registers. Deleting the move preserves the equality test, but changes its final
scratch value to

\[
X_{\mathrm{out}}=\max(x-h-1,0),\qquad H_{\mathrm{out}}=0.
\]

The AX tail uses two such gates in succession. It initially has `A=c`, `D=a`,
`H=b`, and `X=Y=0`. It copies `A` into `X,Y`, checks `X=H`, moves `Y` into `X`,
moves `D` into `H`, and checks `X=H` again. Each equal result clears the already
constructed bundle in `T`. Its intended acceptance condition is

\[
c\ne b\quad\text{and}\quad c\ne a.
\]

After the first mutated gate, `X` has the residue
`r=max(c-b-1,0)`. The move from `Y` adds `c` to that residue. The mutated
acceptance condition therefore becomes

\[
c\ne b\quad\text{and}\quad c+\max(c-b-1,0)\ne a.
\]

These conditions differ. Take `c=a=2` and `b=0`: the first mutated gate leaves
`X=1`, so the second compares `3` with `2` and preserves the bundle despite the
failed freshness condition `c!=a`.

## Exact executable witness

Run:

```sh
python deadloop_counterexample.py --output replay.json
```

The script uses only the Python standard library. It checks prefix-tree
completeness, checks the exact four source substitutions, then independently
interprets every primitive increment, decrement, break, and continue in the
witness. Register order is `(N,T,W,A,D,H,X,Y,L)`.

| Quantity | Original source | Mutated source |
|---|---:|---:|
| Initial registers | `(3,7,0,2,2,0,0,0,0)` | `(3,7,0,2,2,0,0,0,0)` |
| Entry path | `1110100100101011111110` | same |
| Exit path | `111010010011` | same |
| Primitive steps to exit | 58 | 41 |
| Final registers | `(3,0,0,0,0,0,0,0,0)` | `(3,7,0,0,0,0,0,0,0)` |

The seed `T=7` is a convenient positive value for replaying the tail's universal
contract. It is not asserted to be the numerical encoding of the formula bundle
for this tuple. The algebra above applies to any positive initial bundle value:
the baseline clears it and the mutation preserves it. Full primitive traces are
in `counterexample.json`.

This witness disproves the claimed universal AX-tail equivalence. It does **not**
prove that the chosen machine frame occurs along the blank run, or decide
whether the mutated binary machine halts from blank. Such claims would require
additional reachability or global proof arguments.

## A valid smaller cleanup to investigate

At this particular branch, replacing `Move(X,H)` with `Clear(X)` **is** valid:
the branch starts with `H=0`, the following `Inc(H)` supplies the required
positive marker, and the old transfer amount is discarded by the subsequent
clear. This removes one primitive increment from the cleanup loop while
preserving both register effects and the equality branch. The baseline source
does not contain a separate `Clear(X)=N(Dec(X),Continue(1))` subtree, so this
identity alone does not establish a binary state saving.

## Provenance

`original_sites.json` is the exact `reference/candidate245/sites_logical.json`
from the inherited `zfc245-proof-20261018` package, pinned in ProveIt commit
`6d69a46dce1de15397a9d2448dcc946d08c90327`. Its SHA-256 is
`f77a3fb9729382a0b8cd24d480639862b63ecb76bbc205542d1fc7077c025745`.

`mutant_sites.json` was constructed during this investigation by replacing all
four expanded `gm` subtrees with `Inc(H)`. Its SHA-256 is
`6ebc351ed119bdc7d0fcaf6152e7b49b0af48a2771931b318e1fe208c2dace06`.
The independent tree check in this folder reestablishes that relationship; it
does not trust the mutation producer's occurrence count.

The program construction derives from Jeff Ketchersid and collaborators' ZF/m254
development and the ProveIt research. See the retained notices and licenses in
the encompassing contribution. The audit code and algebraic counterexample in
this folder are new work prepared on 18 October 2026.
