# Independent external audit: K coefficient block decomposition

Checker exit 0. Independently Horner-reconstructing the pinned coefficient recipe and dividing its resulting integer into radix-2^47 digits produces 2,021 digits and 253 little-endian byte blocks exactly matching the 11,868-byte raw K0 snapshot. All author block hashes match; there are 126 distinct byte patterns, 128 all-zero full blocks, and a final five-digit/24-byte tail. Input, author checker and result hashes were checked.

This is external Python arithmetic/filesystem evidence for the frozen coefficient recipe. It does not prove that the coefficient array equals Lean's K tile/rank sum, a Lean file/gzip theorem, or JSON/PDF binding.
