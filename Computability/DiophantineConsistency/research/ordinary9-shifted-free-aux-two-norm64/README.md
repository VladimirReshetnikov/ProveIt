# Nine-variable two-norm equation for the shifted free-auxiliary child

`candidate.json` gives a 64-operation equation in nine natural inputs, with four fixed nonnegative integer ports `(beta,K0,MC,MF)`. It evaluates the **exact** first and main residuals A0 and A1 of the shifted-zeta 85-row parent and sets

```text
A0² + A1² = 0.
```

All 64 binary operations and all nine witness inputs are live. The shifted convention remains `k=n_eta+n_zeta+1`. This is a **standard-integer equivalent reduction of the separate shifted-parent free-y² child**, not a proved reduction of the original 85-row parent and not an equation known to characterize Con(ZFC).

## Exact scope of the equivalence

The [84-row shifted free-y² child](../ordinary13-shifted85-free-aux-square-criterion/README.md) retains the original first and main residuals and replaces the auxiliary y² gate by an independent natural input. At a full child zero, its first and main factors are integer units and neither can be −1 modulo 4; consequently A0=A1=0. The checker independently exhausts both generic mod-4 patterns. Hence every child zero projects to a two-norm zero.

Conversely, given any nine natural values and nonnegative ports satisfying A0=A1=0, set the child’s remaining f, i, T and free-y² inputs by the [general nonsquare completion](../../reviews/ordinary13-free-aux-square-general-completion-second-independent/README.md). Here `q=1+beta*J≥1`, shifted `s≥1`, and shifted `k≥1` guarantee `Y>0` and `c=eta+Yk>0`; the completion permits arbitrary signed rank R. It makes the strong and auxiliary factors one without changing A0 or A1, so the child output is zero. Over the integers `A0²+A1²=0` is equivalent to the simultaneous equations, proving the two-way zero-existence equivalence to **that child**.

The original 85-row parent requires its auxiliary y² input to be an actual square. The completion deliberately produces a nonsquare free input, and the parent reverse witness transport remains open. A child or two-norm zero therefore cannot be reported as a parent zero, a proof of inequivalence, or an iPRA consistency equivalence. No full zero is constructed here.

## Exact degree at nonzero beta

With the ports treated as fixed coefficients, the degree is **60 for beta≠0**, including the symbolic compact beta. A direct gate-by-gate syntactic bound would give 68 because it misses a cancellation in A1. Put

```text
U=Yq², a=XY+Y, H=4a+3, c=eta+Yk,
S=U*gamma+R−kbase, B=X+a*c.
```

The literal main root is `U*B+H*S`, and `Delta=a²+H`. The checker verifies the exact integer-polynomial identity

```text
A1 = U²*(X²+2Xac−1−Hc²) + 2UBHS + H²S².
```

In the nine witnesses, `deg(U,X,a,c,H,S)≤(6,2,6,5,6,7)`. The three displayed summands therefore have degree at most 28, 30 and 26. A0 has degree at most 24, so `A0²+A1²` has degree at most 60.

The degree-30 leading homogeneous term of A1 is

```text
8*beta^21 * J^21 * w² * s_input^5 * (eta+zeta_input) * gamma_input,
```

where the names denote the nine unshifted input variables. Its square is a nonzero degree-60 term when beta≠0; A0² has degree at most 48. Equivalently, on the ray setting J, w, the s input, eta and gamma input to t and the other witness inputs to 0, the coefficient of t^60 is `64*beta^42`. Fixed K0, MC and MF cannot affect the leading term because their contributions to S have degree at most 4. The checker verifies the cancellation and the ray coefficient as exact sparse polynomial identities; the degree argument applies to every fixed nonzero beta, with the other ports arbitrary coefficients.

## Reproduction and limits

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary9-shifted-free-aux-two-norm64/check.py | cmp - research/ordinary9-shifted-free-aux-two-norm64/receipt.json
```

The checker verifies the retained first/main expression trees, graph topology/liveness, mod-4 factor exclusions, degree identity and leading coefficient, and reproduces the independent completion review. Its finite and symbolic checks do not constitute Lean elaboration, arithmetic-model transport, proof-object existence, a provider/axiom audit or the missing parent reverse bridge. No Lean or build was run.
