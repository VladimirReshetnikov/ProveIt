Wang943 mixed-radix coefficient backend, B = 2^(5^9)

New result
The complete four fixed coefficients now occupy 977,220 raw bytes.
B-1 has 1,953,125 bits, five times fewer than package19 and25 times fewer
than the previous4094-tile backend. K has 1,958,376 bits. No change to an
arithmetic circuit's variable count, degree or operations is claimed here.

What changed
A radix1024 selector-count digit is followed by radix4 Boolean payload
digits. Selector count is extracted first, after which payload sums are
at most2. Fixed zero-field tests balance mask populations. Exact support
also permits reducing the spatial transport exponent from5497 to42.

Use the entire tuple in this exact order:
  beta, K, MC, MF_source.
MF_source already includes B-1. See COEFFICIENT_BINDING.json for aliases.
Files expanded/*.bin are minimal-width unsigned LITTLE-ENDIAN integers.
The .gz files decompress to those exact values; expanded/MANIFEST.json
records SHA-256, size, bit-length, population and modular checks.

Reproduce with standard Python only:
  python build_mixed.py
  python audit_independent.py
  python load_coefficients.py

No downloaded source program is imported or run. The construction and
independent checker use inert literal JSON. The independent checker also
reconstructs the published package19 tuple and matches all four old hashes,
then separately matches all four new files, geometry and population tests.

COEFFICIENT_PROOF.md gives the complete ordinary mathematical adapter,
including normalized/ordinary interfaces, actual-rank tuning, square w,
odd i, exact popcount(R)=3t+2 and odd s. The universal native/Pell theorem
and literal K215/ZFC-refutation endpoint remain imported dependencies.
This is neither a new kernel proof nor a consistency proof.

Sources are pinned in COEFFICIENT_BINDING.json. The Wang943 language and
anchor/clause geometry are credited to package19; zero-field population
balancing is adapted from package20. Mixed-radix clauses and DR=ρ^42 are
new to this synthesis. No global minimality is claimed.
