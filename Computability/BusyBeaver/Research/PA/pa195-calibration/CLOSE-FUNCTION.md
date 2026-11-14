# PA194 closing of fixed-arity function nodes

`PA194CloseFunction.lean` defines explicit primitive-recursive code
`functionDispatch` for a function term of an externally fixed arity. It
uses certified pairing projections to decode the function symbol and argument
vector, applies a supplied ternary child-closing code to each argument, and
rebuilds the function constructor. The arity controls the size of the
externally generated code: this is not a single uniform model-arity iterator.

`modelMapList` proves the vector traversal equation in every candidate-PRA
model for any externally finite argument list. The list elements, closing
label and binder depth can be nonstandard model values. The parameterized
`modelFunctionDispatch` proves the encoded function-node equation in those
models under candidate-PRA certificates for both pairing projections. The
certificates are available existentially from `PRA_has_stackProjections`; no
particular serialization is fixed here.

`modelShallowDispatch` instantiates the child code with the verified variable
node dispatcher. It closes any externally finite list of bound or free
variable nodes, including nonstandard indices and depths, and handles label
collisions. The external list describes the term's fixed finite shape; this
does not prove traversal of an arbitrary nonstandard term or of nested terms.
`modelFunctionInternal` separately identifies the numerical constructor with
Foundation's named `qqFunc` under an explicit IΣ₁ assumption. No theorem here
establishes the full `closeLabel` operation or a consistency implication.

Run from the repository root with the audited overlays:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-close-function.sh
```
