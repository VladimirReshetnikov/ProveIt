# P3 sparse Rocq certificate manifest

Generated data and certificate shards:

```text
python3 Algebra/PolynomialFormulas/Tools/generate_lazard_root_fourier_numerator_p3_sparse.py --kind coq-bundle
```

The bundle folds a 20,953-term source numerator into five cyclic
rows.  Each row is independently checked against the same
1,218-term normal form.  Data declarations are bounded at
150 terms.  The five coefficient leaves below still ask
[vm_compute] to normalize a complete cyclic row.  They record the intended
equalities, but they are not a viable compilation strategy: the analogous P2
whole-row check timed out after exceeding 13.6 GiB RSS.  Replace them with
bounded staged certificates before adding this bundle to the verified build.
The first file below is the handwritten semantic checker and is intentionally
not overwritten by the generator.

Dependency order:

1. `LazardQuinticRootFourierNumeratorP3Sparse.v`
2. `LazardQuinticRootFourierNumeratorP3SparseDataPart0.v`
3. `LazardQuinticRootFourierNumeratorP3SparseDataPart1.v`
4. `LazardQuinticRootFourierNumeratorP3SparseDataPart2.v`
5. `LazardQuinticRootFourierNumeratorP3SparseDataPart3.v`
6. `LazardQuinticRootFourierNumeratorP3SparseDataPart4.v`
7. `LazardQuinticRootFourierNumeratorP3SparseDataPart5.v`
8. `LazardQuinticRootFourierNumeratorP3SparseDataPart6.v`
9. `LazardQuinticRootFourierNumeratorP3SparseDataPart7.v`
10. `LazardQuinticRootFourierNumeratorP3SparseDataPart8.v`
11. `LazardQuinticRootFourierNumeratorP3SparseData.v`
12. `LazardQuinticRootFourierNumeratorP3SparseCoefficient0Certificate.v`
13. `LazardQuinticRootFourierNumeratorP3SparseCoefficient1Certificate.v`
14. `LazardQuinticRootFourierNumeratorP3SparseCoefficient2Certificate.v`
15. `LazardQuinticRootFourierNumeratorP3SparseCoefficient3Certificate.v`
16. `LazardQuinticRootFourierNumeratorP3SparseCoefficient4Certificate.v`
17. `LazardQuinticRootFourierNumeratorP3SparseCertificates.v`
