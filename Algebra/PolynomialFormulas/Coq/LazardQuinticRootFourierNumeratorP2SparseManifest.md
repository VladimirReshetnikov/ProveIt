# P2 sparse Rocq certificate manifest

Generated data and certificate shards:

```text
python3 Algebra/PolynomialFormulas/Tools/generate_lazard_root_fourier_numerator_p2_sparse.py --kind coq-bundle
```

The bundle folds a 30,282-term source numerator into five cyclic
rows.  Each row is independently checked against the same
1,468-term normal form.  Data declarations are bounded at
150 terms and the expensive reductions are isolated into
five separately compiled coefficient leaves.  The first file below is the
handwritten semantic checker and is intentionally not overwritten by the
generator.

Dependency order:

1. `LazardQuinticRootFourierNumeratorP2Sparse.v`
2. `LazardQuinticRootFourierNumeratorP2SparseDataPart0.v`
3. `LazardQuinticRootFourierNumeratorP2SparseDataPart1.v`
4. `LazardQuinticRootFourierNumeratorP2SparseDataPart2.v`
5. `LazardQuinticRootFourierNumeratorP2SparseDataPart3.v`
6. `LazardQuinticRootFourierNumeratorP2SparseDataPart4.v`
7. `LazardQuinticRootFourierNumeratorP2SparseDataPart5.v`
8. `LazardQuinticRootFourierNumeratorP2SparseDataPart6.v`
9. `LazardQuinticRootFourierNumeratorP2SparseDataPart7.v`
10. `LazardQuinticRootFourierNumeratorP2SparseDataPart8.v`
11. `LazardQuinticRootFourierNumeratorP2SparseDataPart9.v`
12. `LazardQuinticRootFourierNumeratorP2SparseData.v`
13. `LazardQuinticRootFourierNumeratorP2SparseCoefficient0Certificate.v`
14. `LazardQuinticRootFourierNumeratorP2SparseCoefficient1Certificate.v`
15. `LazardQuinticRootFourierNumeratorP2SparseCoefficient2Certificate.v`
16. `LazardQuinticRootFourierNumeratorP2SparseCoefficient3Certificate.v`
17. `LazardQuinticRootFourierNumeratorP2SparseCoefficient4Certificate.v`
18. `LazardQuinticRootFourierNumeratorP2SparseCertificates.v`
