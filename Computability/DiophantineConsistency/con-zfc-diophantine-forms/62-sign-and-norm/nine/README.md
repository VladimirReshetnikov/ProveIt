# Compact nine-positive consistency polynomial

The primary polynomial is `generated/split_116_positive_global.json`:
**9 positive integer unknowns, exact degree 1,834,516, 453 binary operations**.
The nonnegative companion has the same degree and 460 operations.

`PROOF.md` gives the complete new source/binding/calibration proof and the
unchanged free-coordinate finalizer, with its named inherited compiler and
Jones dependencies. The four native ports and every nonliteral final leaf
are supplied as authenticated gzip-compressed signed-magnitude payloads.
`COEFFICIENT_BINDING.json` supplies working local paths for the native
ports. `section.tex` is the report-ready LaTeX section; the root package
builds it into the report PDF.

The source uses the complete compact tuple with native radix 2^590069,
after the explicitly checked row15 adjustment by −beta*J. No individual
ports are mixed between tuples. The target-height improvement is
2161→2068, and the global power chain saves 14 multiplication gates.

Run `python3 reproduce.py` or `python3 -O reproduce.py`. All authored
verification conditions use explicit exceptions and survive `-O`.
The immutable native input is data, not a run of the consistency machine.
The second checker `independent_review.py` imports no project builder or
verifier. Its scope and the author correction to its grouping logic are
recorded in `NOTICE.md`; it is a second finite implementation check.
The outputs `certificates/SOURCE.json`, `certificates/VERIFIED.json` and
`certificates/INDEPENDENT_REVIEW.json` state exactly what was checked.

This is an ordinary mathematical reduction with exact finite certificates.
It is not a new end-to-end Lean/Rocq proof, object-language ZFC derivation,
global optimum, or claimed major breakthrough. It does not prove or assume
Con(ZFC). The comparison snapshot is
`beb0192cb8dc36f78c369c080f2adfbc1887a486`.
