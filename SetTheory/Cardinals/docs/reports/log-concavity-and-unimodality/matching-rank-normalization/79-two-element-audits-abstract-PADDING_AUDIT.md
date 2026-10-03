# Independent audit of old-spanning removal

Approved. Source OLD_SPANNING_REMOVAL.md, SHA-256 27288c835b120a297d03dace6b71342b0afbc2845836418b2a7de5be2652234e.

The parallel-copy reduction is valid for every finite matroid. Add one old parallel copy of each distinguished nonloop; loops need no copy. Parallel extension preserves rank and restriction to the original ground set. Each original distinguished nonloop is in the closure of its added old copy, so the enlarged old set spans the full extended rank. This is exactly the rank-one case of the principal-extension construction already checked in the Bonin–Kung primary source.

Apply the approved spanning-old-set theorem and set each added old variable to zero. Surviving subsets lie entirely in the original ground set, so their basis/extension status is unchanged. This recovers all five Boolean polynomials, including the union U, without a multiplicity or normalization change. The new convention for U0 is essential and correct: it counts original old q-bases of the full matroid, and can be zero; it is not a lower-degree restriction basis polynomial.

The specialized result is nonzero because its no-Y part contains z² times the full original matroid basis polynomial in old variables and the distinguished variables a,b. Every matroid has a basis. Nonnegative linear specialization therefore proves the unrestricted finite-matroid statement. No new derivative case, representation argument or finite enumeration is needed.

Independent check_padding.py verifies86 distinguished-pair padding/restriction identities on10 abstract matroids, including16 initially nonspanning old sets and6 distinguished-loop occurrences. It confirms all five polynomial families and the full no-Y basis decomposition. These checks are supplementary; the ordinary parallel-extension argument is the proof.

Together with the preceding all-matroid extension, the final abstract theorem has neither a representability nor an old-spanning assumption. The head-population weights remain parameters. Directed physical-role merging, a general rank-six graph theorem and a new artifact delivery are not asserted.
