# Independent source review of the 38-witness forward constructor

`check.py` parses the Lean semiring terms independently and compares them to
the pinned 38-witness candidate JSON. All 24 materialized gate assignments
match the residual right-hand sides and appear in their candidate order; every
coordinate they read is an original input or an earlier assignment. The
returned vector puts the 14 input coordinates first, followed by the 24 cut
coordinates, giving `Fin 38 → S`. The port convention is beta, K0, MC, MF
at indices 0, 1, 2, 3; not every port occurs in the constructor. The five
norm residuals are deliberately excluded from this constructor comparison.
The result pins both the source and seed hashes.

This review checks source syntax and ordering only. The constructor imports
the separate uncompiled `SharingGateModel` draft; no Lean elaboration,
kernel check, provider validation, fixed-byte identity, proof that the 24
residuals vanish, norm theorem, reverse reconstruction, Jones instantiation,
or iPRA endpoint is established here. In particular, the source-to-ring
mapping and the natural representatives of the fixed ports remain to be proved
in the relevant models. The authored packet accurately identifies these
remaining obligations.

Run `python3 -I -S -B check.py`; no Lean process was run.
