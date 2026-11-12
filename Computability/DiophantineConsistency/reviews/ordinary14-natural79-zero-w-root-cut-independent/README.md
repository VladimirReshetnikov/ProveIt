# Independent source review: natural-79 zero-w root and divisibility cut

The [source draft](../../research/ordinary14-natural79-zero-w-root-cut-draft/README.md) proposes the correct literal main-root shape and a mathematically valid conditional divisibility chain. It and all cited graph, model, quotient and ring sources remain unelaborated; this is not a Lean theorem, model contradiction, iPRA derivation, axiom audit or physical-file binding.

The pinned 79 DAG's full immutable expression trees have

```
q = 1 + J*beta, X = q*w,
shift = U*gamma - ((n_eta+1)+n_zeta-R),
Dstar = U*(X+a*c) + (3+4*a)*shift,
a = X*Y+Y.
```

The `n_eta+1` and unshifted `n_zeta` are as in the literal source; replacing them with a different shifted form without compensation would change the expression. At `w=0`, `X=0` and `a=Y`. With represented beta, the prior main-norm draft proposes identifying `Y`, `c` and `U` with the corresponding natural-model embeddings, giving `Dstar=U*Y*c+(4Y+3)*shift`. The shift remains a signed difference-ring value; its sign and K0/MC/MF representations are not assumed in this cut. `rfl`, `simp`, embedding rewrites and source-provider resolution remain untested.

The source's witness for `H | U*(d-Y*c)` is valid over any commutative ring: from `Dstar=U*Y*c+H*shift` and `Dstar=U*d`, subtract to obtain `U*(d-Y*c)=H*shift`. The cited signed quotient proposes a possibly negative `d` satisfying the main norm; the separately reviewed ring lemmas would then give `H|U` and `H|3q²`. The displayed final source theorem explicitly assumes the represented beta port, `beta>0`, `J>0`, a graph zero and `w=0`; it assumes no positive gamma, positive root, or represented K0/MC/MF. All these imported results and their composition require Lean checking.

The receipt checks the exact graph expression trees, source signatures, theorem applications and the two unexecuted imported interfaces. Its finite signed witness controls supplement the ring identity; they are not a Lean proof. The signed divisibility is not a contradiction until it is reflected to natural-model divisibility and combined with `0<3q²<4Y+3`. Zero transfer and the iPRA endpoint remain further steps. Both the candidate and independent source receipts reproduce.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural79-zero-w-root-cut-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural79-zero-w-root-cut-independent/result.json
```
