# The complete break1 site at path001

`BreakSite253.paired_break001` now pairs an actual step of the literal
register program with a whole binary dispatch-to-dispatch execution of
the public253 machine. This is one concrete PC site, complementing the
four general register-box excursions.

The leaf at `001` in the existing 6,459-node literal `Prog254` is break1.
Its register step produces path `1` and leaves the infinite register
vector unchanged. The theorem uses that literal program directly; it
does not assume the separate structured219-node DAG bridge.

The binary site contracts are attributed to mira-emmy's PR20, head
`0d544f2a2e3c18f12278441a74b7879f31cbe856`,
`ZF/m253/coq/tm/{Site,SymExec}.v`. Mira-Cult designed the original machine,
Jeff supplied its verification, and Andrew James Wade supplied the
compiler framework. This module is a new Lean proof from the actual
compact253 transitions and the already ported register semantics.

For any natural gap `k`, integer head `h`, finite farther-left tail `L`
and finite register-file tail `Y`, the input zipper is

```text
state33, head h
left, nearest first: 1 0^10 L
right:              0 0 1 0^k 1 0 Y
```

The first left1 is the PC marker. The right1 after the gap is the file
header, and the following0 is the first register separator. The machine
observes that separator and never enters Y. In exactly `2*k+34` Core
steps, the output is

```text
state33, head h
left, nearest first: 1 0^10 L
right:              1 0^(k+2) 1 0 Y
```

The header remains at the same absolute position: both PC-plus-gap
lengths are `k+3`. Every cell in Y and L is retained, including any
nonzero spare data represented there. The right exterior beyond the
finite Y is zero, as specified by the input whole-tape ZipRep. The
return reaches `h-11`, so the ten zeros immediately left of the marker
are explicit requirements. Farther-left data may be arbitrary.

The exact count is five decoder/PC-writing steps, a rightward zero scan
of `k+2` cells, three header-turn steps, a leftward zero scan of `k+2`
cells and a 22-step margin return. The source D0 convention uses
`k=n+37`, giving `2*n+108` steps and output gap `n+39`.

`dispatch_frame_break001` specializes this to the existing
`BootstrapFrame253.DispatchFrame`. Its represented left exterior is
already zero after the marker; `normalize_left_margin` proves that its
arbitrary finite zero-padding length can be represented with ten zeros.
It does not discard arbitrary far-left data. The corollary preserves the
physical primary-register permutation, every spare block, right padding,
the infinite logical zero tail and the lower bound40. It updates only
the represented path and gap. `register_break001` independently checks
the actual register-program step, and `paired_break001` combines both.

The new module compiles with the explicit Lean4.32.0 executable. Sixteen
axiom reports and five caller checks pass. The proofs use only standard
`propext` and `Quot.sound`, with no admissions, custom axioms or native
computation. Nine source-verified dependencies are reused; neither the
full bootstrap nor the register prefix is recomputed. Exact commands,
headers, source hashes, timings and independent review are recorded in
`results/break-site253-verification.json`.

An initial development attempt reduced eight nested raw transitions by
definitional equality and was explicitly terminated. Replacing it with
eight separately checked literal-row rewrites gives the fast final proof;
the interrupted attempt is not a verification result.

No theorem asserts first arrival, that this path has been reached from
the proved RM330 endpoint, or a general decoder/runtime simulation.
For a general path P whose walk stops at depth d, the binary gap view
must also justify that P has no stray one at or beyond d. A geometry-only
DispatchFrame cannot supply that fact. The next general invariant must
retain register-program reachability and prove the no-stray property,
along with the PC-tail splitting lemma that exposes the consumed path.

The full symbolic executor additionally needs scans that can overwrite
their input bit. The actual253 table has non-preserving self-loops at
compact12/read1,16/read1 and78/read0. The current preserving scans suffice
for this concrete site but cannot be substituted for those general
writing scans. General site-checker soundness, all-leaf certification,
enumeration and the internal consistency endpoint remain open.
