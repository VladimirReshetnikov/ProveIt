# Attribution and source boundary

Prepared in Round18 for the ProveIt Con(ZFC) Diophantine work, 25 October 2026.
Public comparison repository pin: e0c98c629bf10d30b695884f6b1d2ab361bdf513.

This component builds on the incoming ConZFC_Cofinal_Anchors_Height_One_Round17
packet and ConZFC_Certificate_Reductions packet. The latter supplies the
ascending-to-descending factorial identity and CRT sign change; Round17
supplies the cofinal one-row semantic anchor, strict x amplification budget,
self-sized radix, consecutive seed coordinates and certified contractions.
The new shift-free positivity bootstrap and its compatible composition are
proved in PROOF.md/report_section.tex. The parent supplied the 42 residual
row shears; their proof is an exact invertible integer change of row basis.

Original licenses are retained under portable/ and the component LICENSE.
SOURCE_MAP.json binds every copied portable/compiler/proof input and records
which compiler files were adapted. build.py derives from Round17's
build_strict_anchor.py; check_affine_export.py and check_natural.py are retained
independent checkers. contract_fixed.py adapts its fixed-priority contractor;
check_semantic.py is an independent adaptation of the Round17 semantic audit.
The TeX renderer derives from Certificate Reductions and independently parses
its literal output back. New finite construction/verification scripts are
supplied with the component license. Historical filenames, notices and proof
fragments retain their original meaning and calibration scope.

No global minimality, literature-wide priority, external human review, new
end-to-end kernel verification, encoded ZFC derivation, or consistency proof
is asserted. Agent reviews are independent workflow checks, not refereeing.
