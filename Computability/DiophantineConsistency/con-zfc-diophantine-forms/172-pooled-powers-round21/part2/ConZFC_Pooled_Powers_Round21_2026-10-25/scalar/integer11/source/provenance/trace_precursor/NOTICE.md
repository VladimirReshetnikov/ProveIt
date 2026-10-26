# Attribution and proof provenance

This contribution was prepared for Vladimir Reshetnikov's ProveIt project
on 24 October 2026, against commit
04a1d79222d55cabe4ba52897863fc33baa8c268.

The existing MIT No Attribution license is preserved at LICENSE.
Unchanged third-party and upstream material keeps its original licenses
and notices under inherited/root_fusion/ and provenance/signed_guards/.

The original incoming root-fusion package is reproduced as a complete
dependency rather than silently incorporated into new code. The new
builders import its small arithmetic-DAG and norm implementations;
build_trace13.py authenticates the exact imported files. verify.py also
authenticates the delivered inherited inventory.

Existing contributions credited in the manuscript include the native
compiler and consistency calibration, the six fixed coefficient tuple,
the signed Pell bootstrap, the determinant and pair guards, the adjacent
coefficient descent, the original five-root norm, and the first-Pell
factorization.

The newly proposed work consists of the full-residue auxiliary
interpolation used in the real-quadratic-safe quintic merger, the shared
positivity/strong witness, the homogeneous product weights, and the
normalized-trace improvement to the thirteen-variable norm.

All mathematical reviews included here are internal independent reviews
from this research session. They do not represent external human peer
review or a proof-assistant verification of the complete theorem.
