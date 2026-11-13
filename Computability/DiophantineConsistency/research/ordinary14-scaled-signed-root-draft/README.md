# Signed scaled root — source-only model draft

This unelaborated source draft strengthens the existing unsigned scaled-square
extraction interface by retaining the **two possible signs**. For an arbitrary
IΣ₁ model, positive natural scale `U`, natural `n`, and difference-ring `Z`
with `Z²=ι(U)²ι(n)`, it proposes a natural `d` satisfying `d²=n` and either
`Z=ι(U*d)` or `Z=−ι(U*d)`. The proposed proof uses the existing source
interfaces `nonneg_or_nonpos` and `scaled_quotient`. It selects neither sign;
proving the appropriate orientation from a graph's own bounds is separate.

The checker inventories the interface, pins the cited sources and exercises
144 bounded integer sign controls. No Lean compilation, provider replay,
physical-file interpretation, graph instantiation or iPRA endpoint is claimed.
All imports, tactics and model coercions remain untested.

Independent source review is recorded in
`../../reviews/ordinary14-scaled-signed-root-draft-independent/`.
