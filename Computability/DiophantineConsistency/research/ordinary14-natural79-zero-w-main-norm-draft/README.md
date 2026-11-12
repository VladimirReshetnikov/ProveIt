# Natural-79 main norm and signed quotient at w=0: source proposal

`Natural79ZeroWMainNorm.lean` proposes the literal main-factor binding needed
for the [forced-w model route](../ordinary14-natural79-w-model-route/README.md).
The source and all of its graph, factor-unit, difference-ring, magnitude and
quotient dependencies are **unelaborated**. This packet does not establish a
Lean theorem, provider or axiom closure, an iPRA proof, or any connection to
physical coefficient bytes or the PDF. Both `#print axioms` commands are
unexecuted.

For an `IΣ₁` natural model, write

```
q = 1 + J*beta,  Y = q³*(n_s+1),  k = (n_eta+1)+(n_zeta+1),
c = (n_eta+1)+Y*k,  U = Y*q²,
N = 1 + (Y²+4*Y+3)*c².
```

`main_eval_cut` proposes evaluating the literal 79 main factor using its
source-only [pattern binding](../ordinary14-natural79-factor-residues-draft/README.md),
for arbitrary signed ports. `atoms_at_zero_w` proposes that when `w=0` and
the beta port is represented by `beta : V`, the literal atoms `a`, `c` and
`U` evaluate to the embeddings of `Y`, `c` and `U`. MC, MF and K0 remain
arbitrary integer ports for these algebraic cuts. The `main_norm_of_zero_w_zero`
client proposes using the [zero-w positive-unit source](../ordinary14-natural79-factor-residues-draft/README.md)
and the generic signed-pair-to-ring source helper to obtain

```
Dstar² = ι (U²*N).
```

Its explicit hypotheses are the represented beta port, a literal 79 zero,
and `w=0`; it does not assume positive w, beta, J, gamma or K0. The zero-w
unit source is itself a draft and is not the 74 factor extractor that assumes
positive w. All unfolding, casts, factor pattern rewrites, `simp` and
`nlinarith` steps still require Lean verification.

The proposed `signed_quotient_of_zero_w_zero` additionally assumes `beta>0`
and `J>0`. The latter can potentially be supplied by the separate
[zero-w guard/J source draft](../ordinary14-natural79-zero-w-jpos-draft/README.md)
when K0 has the required natural-model representation. The scale `U` is
positive because `q` and `n_s+1` are positive; the source retains the stronger
beta and J assumptions used in the eventual argument. It proposes taking a
natural-model magnitude of the actual signed `Dstar`, using the existing
source-level model square-divisibility quotient, and returning a difference-ring
`d` satisfying

```
Dstar = ι(U)*d,    d² = ι(N).
```

Both signs of `Dstar` are handled explicitly; the draft does not assume a
positive signed root or standard-natural prime factorization. The cited
magnitude and quotient declarations are source interfaces only in this packet;
instances, casts, equality rewrites and all underlying providers still need a
coherent Lean check.

This is only part of the `w=0` contradiction. It still requires a literal
zero-w main-root cut of the form `Dstar=ι(U)*ι(Y)*ι(c)+ι(H)*shift` with
`H=4Y+3`; application of the separate commutative-ring divisibility lemmas;
reflection of divisibility to the natural model; and `H>3q²>0`. It also
requires the selected symbolic beta/K0 representations, successor/zero maps,
the natural-80 endpoint, complete elaboration and axiom review. No one of
these follows merely from the finite checker.

The deterministic checker pins the client, graph/atoms/unit source drafts,
generic pattern and model quotient/magnitude source declarations. It verifies
the atoms' copied let block and selected formal source signatures and runs
300 full-DAG integer controls at `w=0`, including signed MC/MF/K0 and varying
gamma, to check `a=Y`, `c`, `U` and the literal main-factor formula. These
finite controls do not prove the unbounded model statement or Lean type checking.

An [independent source and mathematical review](../../reviews/ordinary14-natural79-zero-w-main-norm-independent/README.md)
checks the graph cuts, model interfaces and both quotient signs without
elaborating the proposed proofs.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural79-zero-w-main-norm-draft/check_source.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural79-zero-w-main-norm-draft/result.json
```
