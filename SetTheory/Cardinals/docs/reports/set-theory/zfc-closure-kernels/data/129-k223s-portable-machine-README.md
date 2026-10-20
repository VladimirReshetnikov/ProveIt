# Deterministic construction of the 223-state seed-request candidate

This directory contains a literal deterministic two-symbol, one-tape Turing
machine with **223 working states**, together with the exact source grammar and
an executable reconstruction certificate. The canonical file is
`candidate223.tm`: the working states are `0,...,222`, the start state is `0`, and
`223` is the separate terminal state. The tape is two-way infinite, initially
all zero, and the head initially scans cell zero. A row has the format
`state read write direction next_state`. Both directions are literal `L` or
`R`; there are exactly 446 rows and no transition out of the terminal state.

The canonical table's SHA-256 is

```
c89d3f79ab12a3857092bb4b3d30bfc594079edc0f696b066ce4c386fd00f1b2
```

The intended theorem is that ZFC proves this machine's nonhalting equivalent
to `Con(ZFC)`. The construction changes the upstream 224-state candidate's
set-theoretic axiom emitter to the seed-request presentation `K_s`, and changes
its closed-source parenthesization. The logical calibration and unbounded
binary runtime certificates are necessary parts of that theorem. The present
directory supplies the deterministic source and table layer; the accompanying
report, native seed-request audit, and runtime audit supply the other layers.
No new Rocq or Lean endpoint is claimed.

## Reproduction

From this machine directory, use Python 3.10 or later, with its standard library, and an unpacked copy of the
pinned upstream `K224_Construction_2026-10-20` packet. From this machine
directory, run:

```sh
python3 -B ../verification/../verification/build223.py \
  --baseline-root /path/to/K224_Construction_2026-10-20 \
  --grammar grammar223.json \
  --output /path/to/new-empty-output-directory
```

The optional `--grammar /path/to/grammar223.json` permits storing the frozen
grammar separately from the verification scripts; the command above passes the grammar explicitly because it is stored here.
The standalone script default is a grammar beside the script itself.

The script uses only the four hash-pinned upstream inputs listed in `PINS` in
`../verification/build223.py`. It reads `Dag230.v` directly from the 225-state archive already
nested in that packet, verifies its hash, and treats it as data. It downloads
nothing and runs no optimization or search. The output directory must be new
or empty. Run without Python's `-O` or `-OO` options.

The script reconstructs the literal source and all three machine labelings,
checks their expected hashes, and emits `../certificates/source_certificate.json`,
`../certificates/table_certificate.json`, and `../certificates/reconstruction.json`. A successful run prints
`DETERMINISTIC_223_RECONSTRUCTION_PASS`. A fresh reconstruction of this frozen
candidate passed in approximately 0.27 seconds in the construction environment.
Runtime verification is a separate, slower audit.

## Artifact map

| File | Role |
|---|---|
| `candidate223.tm` | Canonical machine, start 0, terminal 223. |
| `candidate.k.tm` | The same machine in inherited K labels, start 0, terminal 254. Only working state K227 is deleted from the 224-state table. |
| `candidate.legacy.tm` | The same machine in the legacy labels used by the inherited symbolic runtime checker, start 95, terminal 254. |
| `canonical_map.json` | Explicit inverse bijections between K and canonical labels, including the terminal state. The working states are numbered by breadth-first traversal, reading symbol 0 before symbol 1. |
| `legacy_map.json` | Upstream K-to-legacy map. |
| `sites.json` | All 4,962 primitive instruction occurrences, with their complete binary source paths. |
| `grammar223.json` | The literal 77-macro word, exact numerical constructor expression, 164 closed units, unit hashes, and explicit binary parenthesization. |
| `../verification/../verification/build223.py` | Deterministic source and table reconstruction and certificate checker. |
| `../verification/../verification/source_language.py` | Source syntax, closedness bounds, and two independently expressed guarded control-flow resolvers, excerpted from the pinned upstream verifier. |
| `../verification/../verification/local_bisimulation.py` | The upstream finite certificate checker for arbitrary-register equivalence of closed source blocks. |
| `../certificates/../certificates/source_certificate.json` | Nine raw-Dag230-to-optimized-macro certificates, exact emitter binding, and complete guarded control-flow comparison. |
| `../certificates/../certificates/table_certificate.json` | Strict intended-decoder-prefix certificate, all 12 contextual savings, and all 36 retained-row edits. |
| `../certificates/runtime223.json` | Complete blank startup, four induction schemas, canonical conjugacy and full unbounded runtime receipt. |
| `literal_changes.json` | Readable literal transition delta produced by the original compilation. |
| `../certificates/../certificates/reconstruction.json` | Frozen successful deterministic-reconstruction receipt and output hashes. |

## Why the state count decreases

The chosen presentation is the seed-request variant
`seedrequest-s0-p0-r1-o120-hR`: its root conjunction places the hereditary
closure condition before the request condition; its three axiom components
occur in the order membership vacuity, equality helper, seed-request core.
The equality helper remains the upstream `Rel(a,b)` helper. Placing the core
last allows a pair of outer negations to cancel in the native numerical
encoding. More consequentially, the same request block occurs both at the
root and inside closure, so the source grammar can share one more subtree.

| Quantity | Upstream 224 | This candidate |
|---|---:|---:|
| Primitive source occurrences | 4,799 | 4,962 |
| Distinct source nodes, including leaves | 210 | 209 |
| Distinct internal source nodes | 187 | 186 |
| Contextual decoder savings | 12 | 12 |
| Decoder states | 175 | 174 |
| Other working states | 49 | 49 |
| Working states | 224 | **223** |

The final source has maximum path depth 37 and maximum consecutive zero run 6.
The source is longer in occurrences but cheaper in shared decoder states. The
literal table changes 36 retained rows and deletes the two rows of K227.

## Exact numerical binding

Let `P` be the upstream Cantor pairing function and put

```
I(x,y) = 4 P(x,y)
R(x,y) = 4 P(x,y) + 1
Q(x,y) = 4 P(x,y) + 2
E(x,y) = 4 P(x,y) + 3
N(x)   = I(x,1).
```

For natural inputs `a,b,c`, define the following constructor expressions. Here
`c` is both the actual formula code inserted at matrix positions and the
private variable label used by the inherited native decoder.

```
member     = R(b,c)
subset     = Q(c, I(R(c,a), R(c,b)))
found      = N(Q(b, I(c, N(member))))
request    = Q(b, I(c, found))
closure    = Q(a, I(subset, request))
support    = N(Q(a, I(c, N(closure))))
hereditary = Q(b, I(member, support))

membership_vacuity = I(R(a,b), Q(c,R(a,b)))
equality_helper    = I(E(a,b), Q(R(a,b),E(a,b)))
```

The emitted native numerical expression is exactly

```
N(I(membership_vacuity,
    I(equality_helper,
      Q(c, I(hereditary, N(request))))))
```

`../verification/build223.py` independently specifies this expression and symbolically
executes the literal 77-macro word. The result must be identical, while the
arbitrary older stack and its previous top are preserved below the new code.
Each of the nine source macros used for this check is separately linked to
the hash-pinned original Dag230 macro by an arbitrary-register bisimulation.
The arithmetic contracts for those original macros are inherited from the
upstream packet. Thus the numerical binding is tied to the literal source
instructions, not merely to the optimizer's expression input.

## New proof obligations and their certificates

1. **Uniform native seed-request interpretation.** The accompanying theory
   audit relates the displayed code to the seed-request schema and calibrates
   that schema with the original set-theoretic theory. It includes the
   diagonal `a=b` case, handled by existence or absence of a witness and an
   empty or singleton hosting set, and the native total-decoder cases `c=0`
   and `c=1`. The existing gate `c != a,b`, equality helper, membership-vacuity
   helper, and eight logical schema rows are retained.
2. **Literal source computes that numerical expression.** Nine local source
   bisimulations link the optimized macros to their original arithmetic
   contracts. All 164 grammar units are closed. The binary grammar uses each
   unit once in its specified order, and two independent complete resolvers
   agree with the straight sequential composition on all 6,449 guarded
   control-flow checks. Source outside the closed emitter ancestor is reused.
3. **The modified literal decoder implements the intended source.** Every
   internal source-prefix occurrence is checked against the *intended*
   state-to-subtree relation, including the twelve context-dependent aliases.
   This is stronger than assigning meanings to whichever state happens to be
   reached. The table has 223 reachable working states and 446 complete rows.
4. **Unbounded binary execution and exact initialization.** The independent
   runtime audit proves all 6,449 guarded instruction cases with arbitrary
   natural counter values and tape parameters. It covers every one of the
   446 literal rows and uses 1,566,562 symbolic transition steps. The exact
   blank-tape initialized configuration matches the upstream one after
   409,835 transitions, including every nonzero cell, head position, register,
   spare block, and dispatcher label. These are universal symbolic
   certificates and an exact finite initialization check, respectively.
5. **Canonical relabeling.** `canonical_map.json` gives a literal bijection;
   applying it to every transition of `candidate.k.tm` yields the canonical
   file exactly, with start 0 and terminal 223. This preserves every run.

The retained enumeration, proof rules, arithmetic constructor contracts,
source-language semantics, and induction from clean dispatcher frames are the
same upstream obligations used by the 224-state packet. The new logical
presentation, emitter binding, decoder relation, and literal runtime replay
are the parts that must accompany this candidate when it is incorporated in
the repository.

## Provenance

The input packet is `docs/incoming/K224_Construction_2026-10-20.zip` from
`VladimirReshetnikov/ProveIt` commit
`49ee7cfdc8e0364c6db3614675d141d66f9350ed`. All deterministic input hashes are
inside `../verification/build223.py`; all four principal output hashes are in
`../certificates/reconstruction.json`. Research search scripts and failed candidates are not
required to reproduce the delivered machine.
