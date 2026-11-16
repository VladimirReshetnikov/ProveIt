# Source audit notes

The requested Wikipedia and MathWorld pages were read as claim inventories, not as formal specifications. Their notation suppresses several items that are indispensable in iPRA:

- a selected sign convention for the Mellin–Barnes kernel;
- pole separation and a rational clearance from the contour;
- a branch of `Log z` and a positive margin from its cut and from zero;
- explicit convergence margins at vertical and loop boundaries;
- nonresonance for the short fundamental-system formulas, or Laurent/Frobenius jets in resonant cases;
- endpoint, Fubini, Mellin-inversion, and test-class data for integral transforms;
- a boundary convention for step functions;
- base-point constants for negative derivative order.

The report therefore distinguishes literal source wording from the corrected quantitative theorem. DLMF and Wolfram documentation were used to cross-check normalization and selected special cases. The pinned ProveIt snapshot supplies the intended object theory and formalization endpoint, but existing research packets are not silently treated as completed analytic derivations.
