# Sparse MC recipe: external match, failed Lean byte reconstruction

This packet does **not** contain a successful Lean theorem that an MC byte
list decodes to `CompactSymbolicPorts.lowNat`. Three bounded attempts to
compile `RetainedMCSparseBytes.lean` stopped with kernel excessive-memory
errors; none produced an object. Error-recovery axiom reports referring to
the failed `decode_sparseBytes` declaration are not proof evidence.
The third attempt made the natural-power, digit and `ofDigits` operators,
the symbolic values and the support locally irreducible, but still failed.
The exact sources, compiler logs and terminal guard receipts of all three
attempts are retained under `observations/attempt01` through `attempt03`;
all recorded direct dependency and companion guards remained unchanged.
The current attempted source has SHA-256
`ebc234169d5f17764af894e6767a2de3a3530e9e1c6480bd7c0ad076c9499c03`.

The attempted definition forms `sparseBytes` as `Nat.digits 256 sparseValue`,
where `sparseValue` is the sparse complement formula already connected to
the symbolic mask by the earlier `CompactConcreteMask.concrete_bit_recipe`
theorem. Even had this reconstruction compiled, it would have proved
decoding of a **symbolically specified digit list**, not equality to a
literal list extracted from the retained file, or a theorem about gzip.

A separate external check did succeed. `python3 -I -B check_payload.py`
computes the sparse formula using a Python transcription of the source
support:

```
S = (range(943) ∪ [983,993) ∪ [1003,1012) ∪ [1013,1032)
     ∪ {1063,1064,1095,2195,3296}) \ {1}
MC = 2^590069 − 1 − Σ(j in S) 2^(67j) − 2·2^(67·1063).
```

Its little-endian minimal representation matches the decompressed parent
`MC.bin.gz` byte-for-byte. The source support contains 985 entries; the
checked payload has 73,759 bytes and 590,069 bits. The parent binding, gzip,
raw payload and the concrete support source are hash-pinned; all were
unchanged at the external check's sample points. The compressed SHA-256 is
`271fabccdd555bda2c54c4c3a7379cc02eeba4893c07178bfd557a7683b74d5e` and
the raw SHA-256 is
`6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4`.
The successful checker source SHA-256 is
`07e9bdaa0a56c9c7590f61e1538abe1c0e216ae9f208eb693e8623d08304b595`; its
exact output SHA-256 is
`7eb22cf1a6d1bb56bd5094578a6bd6f5e3af5e41b4bd704c030470eaad969cc8`.
The first external checker attempt failed on an incorrect repository-root
path, and the second passed before support-source pinning was added. Their
source and outcomes are preserved separately.

This check relies on an externally transcribed Python support and arithmetic,
Python's gzip implementation, and filesystem bytes. It is not a Lean theorem
identifying a retained byte literal with the sparse expression; the 95-row
supplement's relation to this parent package is another external provenance
boundary. No MC PDF or iPRA binding follows. A further attempt should avoid
whole-value definitional conversion, for example by proving a generic
parameterized radix-window reconstruction, then checking bounded byte
chunks and independently showing their coverage. Such a method still needs
to be implemented and checked; local opacity alone was insufficient here.
