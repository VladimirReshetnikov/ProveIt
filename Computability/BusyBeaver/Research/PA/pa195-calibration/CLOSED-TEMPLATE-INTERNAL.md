# Internal fixed-template closing with model-valued labels

`PA194ClosedTemplateInternal.lean` identifies the fixed-template compiler's
numeric specification with Foundation's actual typed substitution. It builds
a substitution environment that maps each outer placeholder to a bound
variable when its model-valued label equals the closing label, and otherwise
to its free variable; under each internal binder the environment is lifted.
The variable, term, and formula theorems are proved by induction over the
externally fixed syntax template.

`modelBitCloseInternal` and `modelNegativeBitCloseInternal` specialize this
result to the exact bounded-bit template and its negation. The closing label
and both source labels may be arbitrary elements of the model, including
nonstandard values. The theorems explicitly require the candidate-PRA model's
arithmetic reduct to satisfy IΣ₁, because Foundation's typed internal syntax
and substitution are interpreted there. The compiler's numeric structural
equations without this extra assumption are proved separately in
[the fixed-template package](CLOSED-TEMPLATE.md).

This is substitution into an externally fixed template, not a represented
traversal of arbitrary model-valued formula syntax. It does not identify a
general closing code or establish either consistency implication.

Recheck with:

```sh
IPRA_LEAN_OVERLAY=/path/to/project/objects \
IPRA_FOUNDATION_OVERLAY=/path/to/Foundation/objects \
  Computability/BusyBeaver/Research/PA/pa195-calibration/check-closed-template-internal.sh
```
