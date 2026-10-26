# Inverse trace: ten positive unknowns,85 operations,degree232

The single equation is fully specified in PROOF.md and the literal integer-leaf graph equation_bV.json. The new composition saves two multiplications against the pinned incoming Trace_Radical87/232 circuit, while retaining its exact degree232. Every scalar multiplication and square is charged. The full leading homogeneous component has202 terms and is verified exactly.

* `PROOF.md`: complete equation and ordinary unbounded proof at the named native/refutation boundary.
* `equation_bV.json`: all85 live gates,ten strictly positive independent variables,four fully bound integer ports.
* `build.py`: byte-for-byte graph reconstruction from the retained incoming87-gate graph.
* `verify.py`: independent exact polynomial cuts,full leading forms,all coefficient bytes,171 rejected gate mutations,and separately labelled finite recurrence diagnostics.
* `one_anchor7309/`: the same graph at the entire newest coherent tuple,with full native/Pc1 proof and reproducible coefficient reconstruction;172011 raw bytes,largest port345498 bits,big-endian. This is a new compact specialization of an upstream encoding,not a new coefficient construction.
* `inherited_trace/`: unmodified compact subtree of ConZFC_Trace_Radical_2026-10-25.zip at ProveIt892d73e1ab4bc5fd34ecca1967b06dc47ca95494. The original four-port tuple is retained little-endian; its full finite seed recipe is coefficient_recipe.tex.

Reproduce with Python3 and only its standard library:

```sh
python3 -B build.py --check
python3 -B verify.py --receipt /tmp/positive-check.json
python3 -B -O verify.py --receipt /tmp/positive-check-O.json
cmp /tmp/positive-check.json /tmp/positive-check-O.json
python3 -B one_anchor7309/verify.py --receipt /tmp/one-anchor-check.json
python3 -B -O one_anchor7309/verify.py --receipt /tmp/one-anchor-check-O.json
cmp /tmp/one-anchor-check.json /tmp/one-anchor-check-O.json
```

Normal and optimized receipts are supplied. They authenticate exact finite artifacts;they do not certify the unbounded proof or decide consistency. This is an ordinary proof composition with the explicit native/syntactic-refutation calibration,not a new end-to-end formal-kernel object or a global optimality claim. Prepared with AI assistance;internal agent review is not external human endorsement. All inherited sources and licenses are retained.

## Additional interpolation

`q4_interpolation/` supplies a77-operation,degree348 variant obtained by composing the retained q⁴-denominator parent with the trace-linear transformation. Its explicit proof,all gates,byte-reproducible builder and independent checker are included. It fills the76/352→79/290 gap in the incoming five-point trace table;this is a small composition,not a global priority claim. Run `python3 -B q4_interpolation/verify.py` and its `-O` counterpart;all77 gates,33 cuts,35 leading terms and154 mutations are checked.
