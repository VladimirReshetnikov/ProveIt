# A 14-positive-variable equation of degree 34

The explicit polynomial is `pell14_degree34.json`, a division-free DAG in
14 strictly positive integer inputs. It has exact degree 34 and 87 live
binary arithmetic operations. Its five-residual system uses 78 operations
and has maximum residual degree 17. `PROOF.md` supplies both existence
directions; `section.tex` is the report section.

The coefficient tuple is the complete source-34 tuple shared with this
archive. The payload directory is `../coefficients/payloads`; MF means the
already shifted `MF_source`, and all four payloads are bound together.
No coefficient depends on the truth of Con(ZFC).

The new root carrier removes the index quotient h. Its sign is chosen so
canonical completeness uses the positive sum t=gamma+(k-R-1)/(4q^4).
The retained first-root gap rules out first Pell index one before any rank
recovery, and the normalized strong equation permits index recovery without
the ordinary large-ordinate hypothesis. The established positive transport
shift and shared f^2-1 save two gates from the unoptimized 89-gate form.
The source degree-52/79-operation
14-positive forms remain relevant lower-cost alternatives.

Run the standard-library finite verifier from any directory:

    python3 positive14/verify.py

It checks the actual complete coefficient tuple, exact small polynomial
identities, graph liveness/counts, a degree-34 upper certificate, exact
finite-field polynomial rays attaining degree 34, and independent modular
evaluation of the literal formula. Its result is `VERIFICATION.json`.
Use `--coefficients-dir PATH` when testing this component outside the
archive. The main and certificate graphs are rebuilt by `build.py`.

The finite checks do not prove the unbounded compiler equivalence. The new
equivalence proof uses the inherited ordinary native compiler, Pell
classification/index lemmas and syntactic machine calibration. No new
end-to-end Lean/Rocq certificate or global minimum is asserted.
