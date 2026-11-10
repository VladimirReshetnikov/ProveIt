# External MC block-layout reconstruction

The read-only [checker](check.py) extracts six representative little-endian
byte blocks from the pinned gzip/raw MC snapshot and reconstructs all 252
blocks using the nine displayed runs. It separately constructs the matching
`2^47`-radix digit blocks and checks that their concatenation is exactly the
six symbolic run lengths and that each representative block decodes to the
same integer as its byte block. It exited 0; [result.json](result.json)
records the segment counts, snapshot hash and fixture hashes.

Checker SHA-256:
`dd84a5dec47a120bd8064516448ce47afb5522fc555efe226a48cb9001dc8ed9`;
result SHA-256:
`e05f1f4caef342b7cceebf8fae1c25332c6b5be0649e629a79bfd7feaab6751c`.
This is external Python/filesystem evidence; it does not prove the total MC
port equality in Lean, prove a Lean theorem about gzip, or bind JSON/PDF.
The [independent review](../../reviews/nine-sharing-sign17-mc-block-layout-independent/README.md) passed; the packet is frozen.
