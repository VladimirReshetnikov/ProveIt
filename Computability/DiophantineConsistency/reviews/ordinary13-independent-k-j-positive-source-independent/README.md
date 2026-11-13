# Independent source review: independent-k J positivity

The reviewed source `research/ordinary13-independent-k-j-positive-model-draft/IndependentKJPositive.lean.src` proposes that a zero of the exact child graph at the integer casts of an arbitrary **natural** four-port tuple forces its J input positive in an IΣ₁ model. This review found no mathematical or source-interface mismatch. The proof still depends on the separately unelaborated child unit/norm bridge, model casts, tactics and provider closure.

Independently reducing the actual candidate rows at `J=0` gives `b=0`, `q=1`, `X=w`, and

```text
Z = F - (1-F-alpha)*(w+K0),
A0 = Z²,
F=n_F+1, alpha=n_alpha+1.
```

With model-natural `w,K0` and positive shifted F, alpha, `1-F-alpha≤0`, so Z>0. The child `signed_norms` first conclusion gives `Z²=0` when b=0, contradicting positive Z. The source uses the port cast `P72Root.cast_port` at index 1 and the first member of that exact signed-norm conjunction; it does not require beta positivity, an eta/k inequality, X>0, or a fixed compact kernel. The arbitrary-natural-port condition matters: the proof uses nonnegative K0.

The checker pins the relevant sources, reproduces the author's receipt, and independently computes the first root and residual as sparse integer polynomials at J=0. It checks the child witness and port slots, natural cast and signed-norm interfaces, and finite positivity controls. These checks do not validate Lean `simp`, definitional reductions, tactic elaboration, source/object provenance or model axioms.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-independent-k-j-positive-source-independent/check.py | cmp - reviews/ordinary13-independent-k-j-positive-source-independent/receipt.json
```

No Lean, build or staging was performed.
