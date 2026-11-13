# Independent source review: 84→87 unscaling graph binding

This is a bounded source/mathematical review of
`research/ordinary13-unscale84-reverse-graph-model-draft/`; no Lean, builds,
staging or provider replay was performed. The receipt pins the exact graph,
transfer and helper sources, checks both literal row lists against their JSONs,
and reproduces the author's checker output.

The source 84 graph takes s at coordinate 7 and r at coordinate 8. The target
87 graph takes Y at coordinate 7 and a **fresh** positive r at coordinate 8.
The source binds `b=J*beta`, `q=1+b`, `Y=q³*s`, `ell=X*Y²*k` and the
actual signed 84 Bt field. Its source-root and first-residual statements have
the correct unscaled form. The target graph's scaled first root is

```
q³ * (b*(ell+k+r87+s-k*Bt)-Bt),
```

with the essential **plus s**. The receipt independently verifies this
identity and the corresponding q⁶ first-residual factor in a free integer
polynomial ring. It does not claim either full graph output is pointwise
equal or that the graph-field Lean reductions elaborate.

Given a positive 84 zero, positive represented beta and the explicit
`8*X*Y²+4≤k` hypothesis, `reverse_root_of_large` extracts the source first
norm from the first square and calls the separate
`UnscalePositiveRootDraft.shifted_root_of_qcube` with the **same** source
root, Bt and natural tuple. The helper proposes a natural tau and fresh r;
the target first residual uses that tau's norm and the q⁶ scaling. The
result is exactly the proposed `ReverseRootCut` witness: positive Y and r,
the target q³ coordinate equation, and a zero target first residual. It does
not infer positivity of the original source r minus s.

`ReverseInputs p` remains an explicit all-model obligation for the actual
positive 84 zero: the represented natural beta must be strictly positive and
the large-k bound must hold. `reverse_cut` merely packages a supplied
`ReverseInputs p`; this packet does not derive it. In particular, extracting
the actual main norm, including its **extra X*Y*q term**, and deriving large
k are tasks of a separate source client. The source's cast and signed-root
rewrites, imported margin/root helpers, model providers, axiom reports and
endpoint/PDF bindings remain unelaborated.

Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-unscale84-reverse-graph-plus-s-independent/check.py
```
