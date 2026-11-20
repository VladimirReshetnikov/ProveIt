# Effective finite finality

The paper's category section contains the arithmetic theorem and proof. These
files run with Lean 4.32.0 and Python 3. The files Merge.lean and Finality.lean check
the abstract graph and cocone arguments. PathDerivation.lean imports ProveIt's
`ConciseIPRA.PR` and produces object-theory derivations for external path
certificates and merge comparisons. StableQuotient.lean checks the coarseness and
roundwise lifting arguments from the foundations section for a general Boolean
mask operator.

From this directory run

```sh
lean StableQuotient.lean
lean -o Merge.olean Merge.lean
LEAN_PATH=. lean Finality.lean
python3 finality.py
```

For the derivation file, start in a checkout of
`VladimirReshetnikov/ProveIt` at commit
`3ee850b4c2d650cf01263823fd5415963747c5d0`. Set `CATEGORY_DIR` to the absolute
path of this directory, keep the `Merge.olean` built above, and run

```sh
lake build ConciseIPRA.PR
lake env sh -c 'LEAN_PATH="$CATEGORY_DIR:$LEAN_PATH" lean "$CATEGORY_DIR/PathDerivation.lean"'
```

Export `CATEGORY_DIR` before running the command. Only the final command needs
the provider environment. Its imported repository files PR.lean, Deduction.lean
and Syntax.lean were checked against the pinned Git blob IDs.

The Python script constructs comma graphs for valid supplied category and functor
tables. It checks both success and failure against exhaustive small diagrams on
a category with two parallel arrows and a target involution. It checks the
covariant representable at each defect directly. The graph reference code
computes labels; the human proof additionally gives primitive recursive path
tables and their length clock. The Lean datatype `Walk` expresses finite
closure in the metatheory. The numerical internal path representation and
uniform iPRA theorem are detailed in the paper.
