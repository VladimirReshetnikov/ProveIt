# Proposed direct positive-84 main, strong and auxiliary witness

This is an **unelaborated source composition**, not a kernel-checked theorem,
an authenticated provider closure, or a proof in iPRA. It proposes the last
explicit `MainStrongAuxGraphCut` used by the direct 84 q-divisibility source.
The resulting `Positive84ClosedCutsDraft.divCut` has no additional explicit
graph cut, but every imported and newly written source proof, cast, tactic,
model/provider and axiom assumption still requires actual Lean validation.
It makes no claim that the full equation endpoint or PDF is verified.

`Positive84Main.lean.src` proposes to bind the 84 graph's actual signed main
root to P−N after the separately proposed positive-gap rank representation:

```
P = U*(X+a*c)+H*(U*gamma+X*Y*q+R+1),
N = H*k,  a=X*Y+Y, H=3+4*a, U=Y*q².
```

The `X*Y*q` term is retained. The actual main residual yields a signed-pair
square norm. The existing main-parts inequality and positive model scales
orient this **same** root; scaled norm extraction and Pell classification
propose one natural main and one index m with both x/y coordinates and the
same natural balance. No `q | X`, 83→81, or 84→83 assumption is used.

`Positive84StrongAux.lean.src` proposes exact strong and direct auxiliary
bindings for the literal 84 graph. The auxiliary ordinate uses the same
natural R justified by the separate signed-rank cast; it does not assume the
ordinate is positive. The existing 84 first/main norms propose the large-k
inequality, which supplies `1<c` and `0<Delta<c³`. Combined with the actual
positive strong coordinate and existing fact-level auxiliary adapter, these
bounds propose a positive natural auxiliary-offset witness satisfying exactly
the absolute-difference equation required by P72. The main and auxiliary
witnesses share the original graph valuation, rank, c and Delta.

At the compact tuple the source combines that proposed graph witness with the
separately drafted rank-window, early-index, same-index, power and Mersenne
clients. Source-level composition is only a plan for a future kernel check;
no declaration here or in that chain has been elaborated. In particular,
exact graph rewriting, nonlinear ring proofs, model-internal divisibility,
strict bounds, imported theorem interfaces, complete provider ancestry and
`#print axioms` all remain to be checked. The compact symbolic tuple is not a
proof of the external PDF's coefficient or graph identity.

From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-positive84-main-strong-aux-model-draft/check.py
```

The deterministic read-only check pins the direct source bytes, inspects the
actual graph rows and interface names, and evaluates bounded same-valuation
main, strong and auxiliary scalar identities. It does not execute Lean or
prove any graph-zero or arbitrary-model statement.
