# Independent external mask-byte review

The independent checker completed with exit code 0. It compares the decompressed MC and MF_source bytes and hashes from the candidate's external files with independently computed values from the manually inspected, hash-pinned Lean mask recipes. The low mask is reconstructed by digit positions; the high mask is reconstructed as a sum of shifted digits and then shifted by beta. This differs from the author's subtraction/Horner calculation.

The result is an external Python and filesystem check against the inspected source recipes. It does not establish a Lean theorem connecting file bytes, JSON, or the PDF to symbolic ports, and it does not check K0. The Lean sources and external artifacts remain subject to their separately recorded provenance qualifications.
