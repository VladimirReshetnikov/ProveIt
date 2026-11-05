# Physical-order kernel byte recipe for current2011 port 1

[`KernelRecipe.lean`](KernelRecipe.lean) defines a finite natural-number
recipe independently of `CurrentKernel2011.K`: three specified radix powers,
a sum over the 942 physical selector weights (the checked Start weight and the
941 literal sorted certificate rows), and four explicit control sums of 8, 9,
8 and 9 entries. `rawWord_recipe` proves this recipe equals the original kernel
for an arbitrary natural radix. The proof invokes the existing checked
`selector_sum_reindex`, which connects the literal physical-order certificate
to the actual decoded tile table, and the existing `rawWord_eq` decomposition.

`decode_kernel` proves that base-256 decoding of the reversed, canonical
big-endian byte list for this recipe equals `CurrentWindowCarry2011.ports 1`.
The theorem explicitly writes the byte-list expression in its statement;
`bigBytes` is a readability abbreviation. It is not the tautology obtained by
defining bytes directly from `K`: the natural number converted to bytes is the
independent physical-order formula. Its weight table does reuse the repository's
kernel-checked physical-order certificate.

[`check-bytes.py`](check-bytes.py) is a **separate external check**. It pins
and reads the Lean recipe and certificate sources, parses all 941 literal
physical rows and their declared concatenation order, checks index coverage and
descending weights, evaluates the Start selector and all four control sums,
and compares the resulting minimal big-endian bytes with the two K gzip files
referenced by the 67/94 and 67/106 graphs. Both payloads are 11,868 bytes,
94,941 bits and SHA-256
`64a62b9e1eb8642492a159fc5c3a2e1c131a99c0e2f1e3b8b90fac9241166ec7`.
The [observation](bytes-observation.json) and [exit](bytes-terminal.json)
record this comparison. Lean does **not** read or decompress the files; an
external comparison of parsed source rows and bytes is not a formal theorem
about file contents, gzip, TeX or PDF.

[Attempt 01](attempt01/) was an exploratory source-only check of the generic
`rawWord_recipe`: actual session 11828 exited 0, no output object was requested
and no independent input guard was applied. [Attempt 02](attempt02/) checked
all four theorems and wrote an object: actual outer session 98472, dependency
query and Lean compile all exited 0; the log has no warning, error or `sorryAx`.
Each axiom report contains only `propext`, `Classical.choice`, `Quot.sound`.
The object `/tmp/current2011-kernel-byte-recipe-check02-20261105/KernelRecipe.olean`
has SHA-256 `f973fcebb0440d40bc11ef28bb3f45e717599305d0246ec892e3d9a22ce5a073`.

The attempt-02 runner rechecked the prior `FreshModel106` client, sixteen
extension outputs and recorded direct guards, plus the source/base preflight
before and after; both preflights matched the pinned result. It recorded 120
direct dependency, companion and shadow slots. Lean used `-M2800`, one thread,
nice 19, idle I/O and a 180-second foreground timeout. No automatic group-RSS
or host-memory stop was enforced. These are direct input and point-in-time
checks, not an independent base rebuild or complete package-transitive,
dynamic or between-observation ancestry audit.

| Artifact | SHA-256 |
| --- | --- |
| `KernelRecipe.lean` | `13a3b32b1c87156229608a5e8cac2a33a2f85b8b87bec329f35b51cc71ab649a` |
| `check-lean.py` | `b491cb18fbeb6c66a5029c2aca1d8930fccc34cbcf61b6eceea4f6a50feb0fe9` |
| `check-bytes.py` | `058b8f83368ad2bf92b63b36c57e5943b03d7102a3062abfecb7c88332e127d6` |
| `bytes-observation.json` | `47567c37883a1027ae2e3d2e58f28cb24f943d435cced6e775544a35ef3390dd` |
| `attempt02/state.json` | `f752ed2a04fc0ee2638d3687f2555abccf5796f49a10dccf015c05d1a5a0641d` |
| `attempt02/compile.txt` | `5447f01430a0a9a19aa1a3c835d871e3dfb0e2061ff5e8e8bf06e3da764c6a24` |
| `attempt02/outer-observation.json` | `86a9b1fd9ae3abf73890aa8abab3d5793cf6717f6c6f9980e3f3caab7929ac65` |
