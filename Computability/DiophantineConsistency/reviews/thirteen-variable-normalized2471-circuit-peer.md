# Independent proof and finite review of normalized13/71/128

Reviewer: `/root/circuit_reduction`. `/root/complemented47_review` authored
the complete normalized proof, literal graph, auditor and README from ROOT's
normalization lead. I authored neither this packet nor that lead.
This is a separate full review, supplementing my earlier ordinary reviews
of the complete thirteen-variable theorem and the normalization proposal.

I read the complete new173-line proof,375-line auditor, all71 literal
rows and metadata, and the full README. Final reviewed artifacts in
`research/thirteen-variable-normalized-independent/` are:

| File | SHA256 |
| --- | --- |
| PROOF.md | `22670c2f7c35a9e0b88b9505620c924f2a867922cb62464bee0bcf54f752529d` |
| polynomial.json | `50c7d99e5a1abb19f83c9c3b243995d965ecb3d1d39d509d13fd3b18dcec95d4` |
| audit.py | `545084d80681dfcde263b875935d39efddb9812a4a49f6e9805ac8941353991a` |
| CERTIFICATE.json | `f9dfbc842ac0e6c4d6c7bca9fa526a9cfeea1719a17aae6e236b2bdb07aecccb` |
| README.md | `eeec8ffbb2ccc4db2db431420ded54431f0d03d1713a9197c2ffa176f5f2b11d` |

Both read-only commands passed and reproduced exactly the pinned
certificate above:

    python -B research/thirteen-variable-normalized-independent/audit.py
    python -B -O research/thirteen-variable-normalized-independent/audit.py

These commands are relative to `Computability/DiophantineConsistency`.
All guards are explicit exceptions, so optimization does not remove them.
I made no changes to the reviewed packet or its accepted predecessors.

## Mathematics and exact graph transformation

PASS. The entire normalized equation is `P*Q*U*Z-1`, where
`Z=f^2-Delta*(b*i*c^2)^2`. The parent strong factor is exactly `Delta*Z`,
and its full polynomial is exactly Delta times the new polynomial. The
strict positivity `Delta=(a+1)*(a+3)>0` follows on the whole positive
domain before either equation or any native decoding premise. Thus the
whole positive zero sets coincide coordinatewise. Soundness and the
parent's fresh-seed completeness at the full2471 tuple both transport
unchanged. The ordinary proof does not replace a native coefficient or
depend on canonical witness assumptions for its zero-set identity.

The literal rows implement the proposed normalization exactly. The old
products producing S and S squared are deleted; the three products for
`hi^2`, `hi^2*Dc2` and its multiplication by `c^2` replace them. `Dc2`
remains live in the main norm and `Delta*f^2` remains live through Theta.
The old strong subtraction is replaced by the normalized one, the last
product uses it, and the output subtracts1. I checked every changed row
and its dependencies against the complete70-row parent. The count is
40 multiplications,16 additions,15 subtractions. All71 producers, all13
positive unknowns and all four integer ports remain live. No rational
or variable-division leaf enters this graph.

I reviewed the auditor's exact sparse-ring operations and leading-form
propagation. The main norm is expanded in full, with its323 terms and
exact degree18 cancellation, before its leading form is used. Every
other gate's leading form is carried through the actual graph; the
auditor explicitly rejects an unaccounted cancellation. The four exact
factor degrees are22,18,52,36. Their full72-term leading product is the
expansion of

    -128*q0^69*gamma*i^2*k0^11*w^10*s^19*f^10*T^4*C0^2.

Its selected coefficient `-128*beta^71` is nonzero at the fixed tuple,
so the exact degree is128. Multiplication by the full degree12 Delta
leader agrees with the accepted degree140 leader, not merely its degree.
The proof and the literal auditor consistently distinguish polynomial
identity up to the positive factor Delta from pointwise equality.

## Independent reconstruction and validation scope

In addition to reading and running the supplied auditor, I independently
loaded the two complete graph JSON files as data in a separate standard
library calculation, with no project-module import. In a separately
implemented sparse polynomial ring over eight independent cut symbols,
I evaluated both actual output paths and checked `p70=Delta*p71`, including
the complete strong-factor expression. I compared the new output with
a separately written formula `P*Q*U*(f^2-Delta*(b*i*c^2)^2)-1`. The
three-term normalized cut polynomial agreed exactly. An independent
topology/count/liveness walk found all88 symbolic nodes live:71 gates,
13 unknowns and four fixed ports.

I also independently reconstructed every complete2471 integer directly
from the3297-entry coefficient array, the full physical-position set and
the separate native-mask field dictionary. Each complete minimal unsigned
byte string matched its decompressed literal leaf and raw SHA256; their
total is58125 bytes. The bindings are to the entire accepted2471 tuple,
not to the newer2011 native tuple. The standalone auditor separately
authenticates the corrected parent proof, both parent graphs, the parent
certificate, the native theorem and certificate, and every gzip leaf.

The two actual-output/strong-factor mutations are tested against the
symbolic identity itself. The ten further corruptions are actual graph
or metadata changes rejected by the exact expected-graph comparison;
the review does not misdescribe those as ten independent semantic
decision procedures. The physical-marker omission check changes an
actual whole constant. The scoped negative controls are appropriate to
the stated construction and bindings.

No finding or requested correction remains. This is a complete finite
arithmetic alternative with the ordinary inherited native and syntactic
contracts. It does not supply a new page, unrestricted-variable lift,
fresh formal-kernel replay, consistency decision or global minimum.
