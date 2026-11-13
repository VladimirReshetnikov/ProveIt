# Independent review: AQ17 factored root

This read-only external review checks the 17-variable, 94-operation, degree-20 positive graph and its 111-operation natural shift. Run `python3 -I -S -B check.py` from any directory and compare with `result.json`; the author's checker and receipt also reproduce. No Lean, staging or provider audit was performed.

The checker independently expands both complete outputs over all 17 inputs and four symbolic ports. All 3,598 integer polynomial terms match, as do all eight named residuals. All graph rows, variables and ports are live, and the natural graph is the exact shared positive shift. This establishes the equality for arbitrary integer valuations and ports; it is stronger than a zero-set correspondence. Its local factorization uses distributivity of `q³*qm*firstDelta + Bt*q³`.

The output has input degree 20, witnessed for every fixed integer port tuple by the port-independent `Y⁸*eta⁸*i⁴` term of coefficient 1. The equation's positive-domain zero-map hypotheses and upstream beta requirements are inherited from the [17/95 graph review](../adaptive-aq17-positive-bindings95-independent/README.md). Neither this new syntax nor the previous reduction chain has an elaborated Lean model transfer or iPRA endpoint; the external identity does not authenticate historical provider ancestry, physical PDF semantics or global minimality.
