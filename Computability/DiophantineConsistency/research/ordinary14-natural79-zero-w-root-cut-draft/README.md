# Natural-79 zero-w root cut and signed divisibility: source proposal

`Natural79ZeroWRootCut.lean` proposes a literal main-root cut and a client of
the [unelaborated signed-main-norm draft](../ordinary14-natural79-zero-w-main-norm-draft/README.md)
and the two [unelaborated commutative-ring divisibility lemmas](../ordinary14-natural79-w-model-route/README.md).
All these declarations, imports, casts, tactics, provider objects and axiom
reports remain **unelaborated**. This packet does not establish a Lean theorem,
iPRA derivation or physical coefficient/PDF binding.

The graph's existing `atoms` builder exposes `U`, `a`, `c` and `Dstar`; its
`rank` field exposes `R`. This source defines the literal expression

```
X = (1 + J*beta)*w,
shift = U*gamma - ((eta+1)+zeta-R),
Dstar = U*(X+a*c) + (3+4*a)*shift.
```

The values of `eta`, `zeta` here are the **unshifted input slots**, so the
`eta+1` term is part of the displayed shift. `root_expr_shape` proposes an
exact `rfl` literal-expression equality for arbitrary signed ports. At the
natural-model valuation `w=0`, `root_eval_zero_w` proposes eliminating `X`
over the difference ring, without a represented-port, positivity or zero
assumption. If the beta port is represented by the model element beta, the
prior source proposal `atoms_at_zero_w` identifies `a=Y`, `c=c` and `U=U`;
`represented_root_zero_w` then proposes

```
Dstar = ι(U)*ι(Y)*ι(c) + (4*ι(Y)+3)*shift.
```

The shift may be negative and its graph expression contains arbitrary signed
K0/MC/MF ports. No sign or representation for these three ports and no gamma
positivity are assumed for this root cut. The syntactic source checker verifies
the corresponding external graph expression trees and finite controls, not
that the proposed `rfl`, `simp`, or casts elaborate in Lean.

`divisor_of_root_cut` supplies an explicit commutative-ring witness: when
`Dstar=U*d` and the root cut holds, `(4Y+3)` divides `U*(d-Y*c)`. The final
source client invokes `signed_quotient_of_zero_w_zero`, then the existing
`divisor_of_main_norm` and `divisor_of_three_square` proposals. Its explicit
hypotheses are a literal 79 zero, `w=0`, beta represented in the difference
ring, `beta>0` and `J>0`. It proposes the **signed difference-ring** conclusion

```
(4*ι(Y)+3) ∣ 3*ι(q)*ι(q).
```

The root quotient can have either sign; no positive-root assumption is made.
`J>0` must be supplied separately, for example by the unelaborated zero-w
J-positivity draft under its K0 representation and nonnegativity assumptions.
The conclusion is not yet a contradiction: it remains to reflect this signed
divisibility back to natural-model divisibility and prove `0<3q²<4Y+3`, then
connect the resulting `w>0` to the natural-80 zero and iPRA endpoint. All
three included `#print axioms` commands are unexecuted.

The deterministic checker pins the proposed source, the graph JSON, atom and
signed-main-norm drafts and the abstract ring lemmas. It verifies the exact
unexpanded graph AST for the literal root/shift, plus 300 modular evaluations
at `w=0` with arbitrary signed ports. These controls do not prove Lean's
semantics, the source theorems, imported provider/axiom closure, or the
remaining divisibility/positivity claims.

An [independent source and mathematical review](../../reviews/ordinary14-natural79-zero-w-root-cut-independent/README.md)
checks the literal cuts and ring divisibility implications without
elaborating the proposed model statements.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural79-zero-w-root-cut-draft/check_source.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural79-zero-w-root-cut-draft/result.json
```
