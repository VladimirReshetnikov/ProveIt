# Independent review of the split108 signed-ten composition

This is a source-placement refinement of the reviewed split116 signed-ten composition, not a new Sun interface. The two-root finalizer, congruence normalizations, completeness restrictions and whole four-port tuple are unchanged. The source is globally negated after the same two invertible row shears. Global negation preserves the common zero set and does not change the borrow-tolerant zero test.

The revised parameters are M=108, Q=1939, kernel degrees 1939,1842,1738, H=1954, N0=B^109, N1=B^1955 and N=B^2064. Thus H=max(1939,1842+108,1738+216) as required. Its three leading coefficients are 2,2,beta_native, all positive. Since every lower coefficient has absolute value below C0 and B>4096 C0 b², each kernel is positive by geometric-tail domination, before assuming a binary base. This simplifies the former cross-kernel leading-layer dominance argument.

The mask population is (109+22)v−31k−22, so the required threshold exponent is 1+2064v+(109+22)v−31k−22 = 2195v−31k−21. With v=kappa+2k this becomes 2195 kappa+4359k−21, precisely the stated Y=2^(2195 kappa−21)b^4359. Target count22, coordinate count31 and strictly positive weights are unchanged, so every b/mod3 argument and completeness divisibility in the split116 audit remains valid.

The supplied independent checker applies the negation and shears itself and verifies sparse source extraction. It passes in fresh copies in ordinary and optimized Python (REPLAY.json). A separate topology/liveness/degree-propagation pass confirms ten variables, 520 binary operations and degree upper bound3,327,948 (STRUCTURE.json). Its supplied nonzero leading-coefficient tests with actual payloads establish exact degree at that bound. Snapshot hashes preserve the reviewed bytes.

No mathematical incompatibility was found. This review inherits the explicit compiler and Sun theorem boundary and does not claim a new end-to-end proof-assistant certificate. The source refinement improves both degree and count over split116's 3,671,340/522; it does not dominate the large-degree 513-operation baseline on operation count alone.
