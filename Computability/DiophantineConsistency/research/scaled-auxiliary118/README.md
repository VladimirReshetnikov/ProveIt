# Sorted2501 with a degree-118 auxiliary factor

This packet gives a complete integer-leaf equation with fourteen positive
unknowns, 66 binary arithmetic operations and exact total degree 118.
Its four fixed integers are exactly the accepted sorted2501 tuple: their
minimal unsigned big-endian encodings total 58,829 bytes. It preserves
the entire positive zero set of the accepted Carrier65 equation by the
identity map on all fourteen unknowns. The 65-operation, degree-150
equation remains a separate checkpoint; the new equation is a degree
improvement at a cost of one operation.

The ordinary proof is [PROOF.md](PROOF.md), authored by ROOT from an
inert reading of the credited orientation manuscript. No incoming
executable was run. The complete graph [polynomial.json](polynomial.json)
and standalone finite [audit.py](audit.py) were newly authored by
`complemented47_review`. Their retained parent is the entire
[sorted2501 Carrier65 graph](../../candidates/one-page-sorted-carrier65-2501/polynomial.json),
not an isolated Pell gadget. Every one of its old producers remains live.

The only changed coefficient in the arithmetic front is

    A = Delta*f^2-Delta,
    Unew = A*(V^2-y^2)+y^2,

in place of `U=S^2*(V^2-y^2)+y^2`. `Delta*f^2` is already a live
parent producer, so one new subtraction suffices after rescheduling it.
The counts are 37 multiplications, 16 additions and 13 subtractions.
The evaluator uses only integer leaves, addition, subtraction and
multiplication; the mathematical proof's cancellation by a positive
integer does not introduce division into the graph.

At a positive zero of either equation, the common factor
`Z=Delta*(f^2-Delta*i^2*c^4)` equals `Delta`. Its quotient must be an
integer unit, and its residue modulo four excludes the negative unit.
The exact identity
`pnew-p=P*Q*W*Z*(Z-Delta)*(V^2-y^2)` proves both zero-set directions
before any sign interpretation of `C`, `R`, `tau` or `V`. In particular,
this transfer covers noncanonical positive solutions as well.

The complete finite audit checks:

- All 66 literal rows, every metadata field and exact parent-to-child
  transformation, topological dependencies, integer leaf types and the
  liveness of every gate, all fourteen unknowns and all four fixed ports.
- The entire 323-term main-norm expansion, its cancellation identity,
  and every gate's complete leading homogeneous form. The five factors
  have degrees `22,18,30,2,46`. The certificate includes every term of
  each factor's leading form and all 40 terms of the degree-118 leader.
  Its selected coefficient is `-8*beta^68`, with the actual nonzero
  coefficient magnitude also computed and hashed.
- The four exact polynomial identities used in the proof, by independent
  symbolic expansion at the shared subexpressions, and all 256 residue
  cases modulo four. The ordinary positivity and integer-unit arguments
  remain explicitly in the proof.
- All 3,297 pinned native coefficients, direct reconstruction of the
  complete four integers, equality to the final native certificate and
  to each accepted gzip materialization, and the actual scalar bounds.
- Seven graph/metadata corruptions, a wrong-sign polynomial-identity
  control, and a physical-marker omission that changes the complete
  mask integer.

From the repository root, both read-only commands reproduce the exact
certificate bytes and passed after the complete script was read:

```sh
python3 Computability/DiophantineConsistency/research/scaled-auxiliary118/audit.py
python3 -O Computability/DiophantineConsistency/research/scaled-auxiliary118/audit.py
```

The explicit `--write` mode writes only `CERTIFICATE.json`; normal and
optimized default modes do not modify any file. Every gate is an
explicit `require`, so optimized Python preserves the checks. The audit
does not import any repository executable and does not search for zeros.

Frozen artifacts:

| Artifact | SHA256 |
| --- | --- |
| `PROOF.md` | `b2cb3b703da36bb33e1a3d26851d139a246010f1b2a39491927d6ea43031bd7f` |
| `polynomial.json` | `588f295e6d965ff5f7b78deda02b808575aaf818908af528a738a98ecda5c72f` |
| `audit.py` | `d15c556f0d8c9cb22299848061689df600e0782a663dcfe2ce7adde94d94bd06` |
| `CERTIFICATE.json` | `add251dae98487ca9f0d278f14013331c9381ca24be84c5df6f13458ee348b0f` |
| Complete sorted2501 parent graph | `06be4bd16a817fe8de0042dad0f3c0f7f93ac310959798a132fb5f18c0ffe035` |
| Native ordinary proof | `d38b5f83ae1b6d342d849e134e1fa341306cb506d68f58fbe74abf9e013cb65d` |
| Native finite certificate | `372cee7b5e353ee174a9335e117c843b0e847892b038847bcb5df4c6dda8feae` |

The independent [mathematical review](../../reviews/scaled-auxiliary118-math-peer.md)
was written before its reviewer authored these finite artifacts, and
states that separation of roles. A second
[ordinary proof review](../../reviews/scaled-auxiliary118-circuit-peer.md)
is independent of both the proof and artifact authors. The independent
[root finite-artifact review](ROOT_FINITE_REVIEW.md) now passes after a
complete code/graph review and normal/optimized read-only reruns. ROOT
authored the ordinary proof; that role is separate from reviewing these
artifacts, which were authored by the mathematical reviewer.

This is an ordinary proof transfer through the accepted complete native
and Carrier65 theorems. It adds no new formal-kernel replay and does not
decide `Con(ZFC)`. Scalar bounds alone do not attach a consistency
interpretation to arbitrary four integers: the pinned sorted2501 tuple
and its retained syntactic calibration remain essential. No new printed
page is claimed here, and the accepted page has not been changed.
