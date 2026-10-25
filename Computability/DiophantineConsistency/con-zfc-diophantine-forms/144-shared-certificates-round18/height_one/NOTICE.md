# Attribution and scope

The Round17 incidence-local compiler, affine factorization, quartic pair equality,
unit path, literal printer, independent arithmetic audit, and the predecessor
shared-incidence compiler are retained with their original attribution and
license. Files in upstream/ are byte-identical copies from the inspected
ConZFC_Cofinal_Anchors_Height_One_Round17_2026-10-25 archive, apart from no changes.
The source original263 and original285 files are exact copies of this release's
signed-reduction outputs; SOURCE_BINDINGS.json records their hashes and theorem
interfaces.

Round18 contributions here are fixed row-sign balancing, fusion of opposite
identical normalized occurrences into direct row-to-row edges, and coefficient
normalization using smaller already-needed addition chains and shared scale
factor vertex covers. The independent checker is an adaptation of the Round17
producer-free audit; it does not import the compiler. All evidence boundaries
in proof.tex apply. No consistency proof or new complete formal-kernel theorem
is claimed.

comparison/old_polynomial.json, old_certificate.json, old_audit.py, and
ROUND17_MANIFEST_SHA256.json are unchanged historical Round17 inputs. Their
original paths and byte hashes are checked by compare_matched.py. They are
comparison evidence, not additional new endpoints.
