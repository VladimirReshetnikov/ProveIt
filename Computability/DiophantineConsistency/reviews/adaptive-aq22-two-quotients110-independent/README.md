# Independent review: two AQ22 scaled-root quotients

This read-only review checks the 22-variable, 110-operation, degree-10 positive graph, its 132-operation natural shift and the existing quotient lemma source. Run `python3 -I -S -B check.py` from any directory and compare with `result.json`. The separate author checker and receipt also reproduce. No Lean build, staging, new endpoint proof or provider audit was performed.

The parent JSON's 22 variable bindings, four ports and 114 rows match the pinned `AdaptiveAQ22Literal` source. The child replaces the two positive parent roots with quotient variables and reconstructs them as `z=scale*first` and `d=mainScale*main`. The new root-binding residuals agree with the parent residuals under this reconstruction. The parent norm residuals become `scale²*child.A0` and `mainScale²*child.A1`. Both outputs are independently checked to be sums of the same 13 formal residual squares.

The checker expands the **entire** outputs over symbolic inputs and four arbitrary integer ports and verifies the stronger identity

```
parent(lift child) - child
  = (scale⁴ - 1)*child.A0² + (mainScale⁴ - 1)*child.A1².
```

The correction polynomial is nonzero, so the reduction is about zero sets rather than equal outputs. The 1,514-term child expansion has degree ten, including the port-independent monomial `deltaVariable²*f⁴*y⁴` with coefficient 1 and no other term with that input monomial depending on ports; its exact degree remains ten for every fixed integer port tuple. All positive graph rows and inputs are live; the natural graph is the exact shared `x=n+1` shift.

The source of `ArithmeticAdaptiveQuotients2011.scaled_quotient` explicitly quantifies over `V` equipped with the model arithmetic structure and IΣ₁, requiring `0<m` and `z*z=m*m*n`, and concludes `∃t, z=m*t ∧ t*t=n`. Its source invokes the model-specific `ArithmeticSquareDivisibility.dvd_of_square_dvd` and positive-scale cancellation. For a positive parent zero, both squared-norm residuals vanish and both scales are positive, so the lemma applies independently to the same original valuation; positivity of each original root and its scale makes each quotient positive. The remaining residual identities then give a child zero. A positive child zero lifts by the displayed products. These arguments use the ordered-model sum-of-squares property and work for arbitrary signed fixed ports; a Lean proof that connects this particular 110-row literal and these identities to that existing lemma remains open.

The pinned parent `IPRAAQ22Native.literal_equivalence` is for the positive shift of the parent literal and the mapped native refutation formula. Its historical paired replay matched 37 added modules with an independent full artifact audit. The historical task-policy pins the very same parent literal and native endpoint source hashes used here. The matched replay retains its inherited provider, runtime, package-transitive and Foundation-wrapper limitations; the standard-theory result is qualified by the recorded chain. This review does not upgrade those results or establish a compiled internal iPRA theorem for the 110-operation candidate, an untranslated classical Con(ZFC) identity, or PDF semantics.
