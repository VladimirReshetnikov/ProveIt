# PA194 term closing dispatch

`PA194TermDispatch.lean` connects the encoded bound-variable, free-variable,
and function-node cases. Its explicit primitive-recursive dispatcher tests
the node tag and, for a function node, maps a supplied child-closing code over
a fixed externally chosen arity before rebuilding the encoded function node.

`modelBound`, `modelFree`, and `modelFunction` prove the exact constructor
equations in every candidate-PRA model, assuming certificates for the two
pair projections. Labels, indices, depths, symbol codes, and vector contents
may be nonstandard model values. `modelShallowFunction` specializes the child
code to the verified variable dispatcher and closes a function whose externally
finite list of children consists of arbitrary bound/free variable nodes.

The named Foundation `qqBvar`, `qqFvar`, and `qqFunc` identifications are
separate theorems requiring IΣ₁. The code is not a single uniform arbitrary-
arity or arbitrary-height term traversal: `k` is fixed externally and the
function branch takes an explicit child-closing code. In particular this does
not establish generic `closeLabel`, the formula translator, or an iPRA
consistency implication. See [CLOSE-FUNCTION.md](CLOSE-FUNCTION.md) for the
underlying vector traversal and the existential projection certificates.

Run from the repository root with the audited overlays:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-term-dispatch.sh
```
