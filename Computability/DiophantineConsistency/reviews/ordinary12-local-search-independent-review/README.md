# Independent review of the 95-gate local-search prefilter

The reviewed `search.py` SHA-256 is
`98f54938a6eb1a158ffca98581dd5836300e13a6d07f9340ca52ab8ae55f3949`;
its recorded output SHA-256 is
`900114673aa4ee10229634754abfa5af5a02f292c4d29a9af498eddba2e096af`.
The independent captured run exited 0 and reproduced the complete output
byte-for-byte. The graph, binding, four compressed payloads, search source
and prior output were unchanged at the recorded postchecks. The four fixed
port residues computed independently from the pinned minimal little-endian
payloads agree with the output: beta `817662899`, K0 `793709379`, MC
`208478425`, MF `412017042` modulo `1000000007`.

I reviewed the search's topological operand pool and liveness calculation.
It enumerates first gates using unordered pairs for commutative `+` and `*`,
ordered pairs for `-`, and considers the fresh gate as either side of the
second subtraction. A second multiplication by a prior operand uses modular
inversion, and squaring the fresh gate uses both roots in each of the three
samples after verifying the prime is `3 mod 4`. The source output reports no
zero sampled targets or nonconstant operands in either pass, so an omitted
inverse for literal zero cannot match any sampled target. A synthetic
zero-valued node and a separate fixed-zero-port test set the corresponding
guard counters; the main program checks those counters for both passes.
It does not literally enumerate `t+t` or `t-t`: the former has the same value
and live count as the enumerated `t*2`, and the latter cannot equal any
nonzero sampled target.

[`audit.py`](audit.py) extracts only the frozen source's helper functions
and compares their candidate sets and live counts with an independently
written, direct exhaustive enumerator on six small DAGs, including a fixed
port, square and reverse-subtraction examples. All comparisons matched.
Mutating the extracted search to omit square candidates, omit reverse
subtractions, or count all gates instead of reachable gates was detected by
the exhaustive comparator. The positive control in the actual run finds
both the one- and two-gate reductions of its deliberately redundant output.
These tests are not an independent exhaustive rerun of all candidate gates
on the full 95-row graph; the full pinned search itself was rerun exactly.

The search compares replacements with the **selected node's value**, not
with the final output alone. It can miss a replacement that changes that
node but preserves the final polynomial through its downstream context,
such as sign reversal under a square. Its unrestricted-port pass rules out
survivors only among identities uniform in the four symbolic ports, while
its fixed-port pass uses those actual coefficients modulo one prime. Both
are external modular filters: they establish no Lean theorem, global size
lower bound, or exclusion of rewrites outside the stated local class.

`python3 -I -B run.py` produced the captured exit-0 receipt in
[`terminal-attempt04`](terminal-attempt04/) and result in
[`observations-attempt04`](observations-attempt04/). The run source SHA-256
is `27e113723fbddb56f703a0e3c1e628ae092e9b2c9165434a1d669ec10ddb5273`,
the audit source SHA-256 is
`5af89a1b2ec8e8b34bd08a49592cad23fcbf2bd7db771f607dfec3f183a2bcf4`,
and the audit result SHA-256 is
`d7efe7ba6936d6ef340ac5fba9474f99223231cc330f9670fc14325abd756e15`.
The terminal receipt SHA-256 is
`752aefbf36b7485face554b754e1311264afa4f40bc85d1c6d4e9f19d6379f56`.
Prior successful audit versions are retained in attempts 01–03. Filesystem
guards are point-in-time, and payload decoding/transcription remains
external to Lean.
