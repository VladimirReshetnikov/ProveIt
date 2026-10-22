# Independent architecture and trust audit

Repository pin: `6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95`.

## Established baseline and scope

The maintained phase-fourteen checkpoint reports 178 Lean project modules in
the exact K215 endpoint closure, selecting 2,093,112 source bytes. Its current
endpoint theorem is

```lean
BlankHalts machine215 ↔ BProv ZFCax_s [] Form.fBot
```

The corresponding nonhalting theorem negates each side. The maintained Rocq
lane reports 237 selected sources, closed endpoint assumption reports, and a
recursive `coqchk` audit. These are the repository's existing evidence, not
fresh whole-endpoint results from this research session.

The repository expressly distinguishes these external proof-assistant
theorems from an internally encoded PA endpoint, which remains open. An
adapter or component theorem must not be described as a new proof of the
whole exact-table endpoint until its full affected import closure and typed
endpoint clients are checked.

## Prior work that must be attributed

The proposal index already contains normalized and balanced certificates,
source contraction to a 367-vertex affine core, positive simulation,
semantic site contracts, uniform decoder prefixes, a checked complete
decoder-prefix/residual component, shared implication derivations, dense
one-invariant transport, candidate scheduling, and a CP/GIC-to-QHyp adapter.
The last adapter is an existing proposal with a reported 25-module component
check; it is not the new contribution of this session.

The direct full-seed route is explicitly proposed in
`proposals/sharing-interfaces/calculus/DIRECT_FULL_SEED.md`, and the underlying
Rocq route already exists in `rocq224/src/Complete222.v`. The contribution of
implementing it now is a checked Lean realization, integration, and precise
accounting, not the discovery of the mathematical construction.

## Independent check of the direct full-seed argument

The decisive type is `KEind222.c222_complete`. For an arbitrary named theory
`T`, its syntactic input is derivability of `enc (th f)` for `f ∈ T`, whereas
its semantic countermodel input satisfies `f` itself with literal equality.
Its proof imports `KThmK` and `KEqCodes222` and does not depend on the later
seed-model or indiscernibility modules. Thus a direct full-seed construction
using this interface is not circular.

For a named matrix ψ, let p be its double negation and let c = enc(th p).
Use the named bundle with input label 0, output label 1, private container
label c, and matrix p. There are four genuine obligations:

1. c > 1, so the numerical bundle row is enabled.
2. c is not free in p. This follows by preserving free-variable support
   through `th` and proving every free name of a formula is smaller than its
   encoded number. It is a statement about free support, not all syntactic
   occurrences.
3. `th` commutes with the named bundle: its newly introduced atoms are
   membership atoms. Therefore the interpreted encoding of this named
   bundle is exactly the numerical enabled bundle.
4. A named bundle with these freshness premises is semantically equivalent
   to the seed property of its named matrix. This theorem uses literal
   `NF.bot`, so it does not need irreflexivity internally. The numerical
   bundle theorem still needs irreflexivity, because decoded code 1 is a
   self-membership atom.

Applying the semantic theory hypothesis to that named bundle, then removing
double negation pointwise, gives every named seed instance on the original
domain. The endpoint can use `e 0` as its inhabited-domain witness. The
tagged domain, bisimulation quotient, well-founded part, and ZF model
construction all remain; only the preliminary indiscernibility quotient
becomes unnecessary in this endpoint's closure.

Compatibility requires placing the `FullSeed` and `DerivableNF` interfaces
where both old and new clients can import them without a cycle. Old public
quotient theorems can remain in their optional module. Import pruning must
be measured after this move, not inferred from the obsolete module's line
count.

## Independent check of the Rocq duplication target

The fetched `ZF/L1_LProp.v` and current `K215F/L224Prop.v` each contain
71 `Lemma` declarations. Replacing `mllp` by `llp`, `mlpc` by `lpc`, `MDET`
and `MB1`–`MB3` by `LDET` and `LB1`–`LB3`, and `lprov224` by `lprov` makes
all 71 statements and all 71 proof bodies identical after whitespace
normalization.

The carrier-specific term `Weq 0 0` occurs only in the proof bodies of
`llp256`, `llp275`, and `llp330` (four occurrences in each), never in their
statements. Every one of these lemmas already binds a formula `w0`, which
can replace that arbitrary term. Consequently the shared core does not
need equality, a distinguished formula, or an inhabited-carrier premise.
Its true parameters are a formula carrier, implication, negation, a
theorem predicate, modus ponens, and the B1/B2/B3 axiom rules.

The mathematical proof bodies remain inherited proofs. New work is the
representation-independent packaging and the actual adapters preserving
all exported names. A `Module Type` contract is not an added endpoint
axiom if each concrete adapter supplies its fields by the existing
constructors and the instantiated assumption reports are closed.

## Changes to reject or keep separate

- Restricting the numerical soundness theorem to well-formed decoded
  formulas, or silently dropping coincident role names, does not preserve
  the current theorem. The machine intentionally computes with arbitrary
  natural codes.
- Sharing generated data is not by itself proof sharing. Count the new
  checker/interface and every compatibility wrapper in the comparison.
- A shorter definition with a stronger unproved hypothesis is not a
  simplification of a closed endpoint.
- A component checked in Coq 8.18 is useful evidence but does not substitute
  for the production Rocq 9.1 integration gate.
- Replacing repeated derivation bodies by opaque axiom declarations is
  unacceptable. Closed concrete assumption reports are the relevant gate.
- An old receipt proves only the exact source/import bytes it binds. It
  cannot certify a newly combined set of otherwise successful patches.

## Required acceptance evidence

For the direct-seed Lean change: compile the support and named semantics,
compile the original endpoint theorem type through the new lower bridge,
print its exact assumptions, compare the final overlay import closure to
the pinned baseline, and compile the old public interfaces as explicit
compatibility clients. A full physical site replay is necessary only if
its source/import binding changes; an unrelated semantic edit need not
repeat a byte-identical runtime check when the repository's provider
reuse policy applies.

For the Rocq core: compile both concrete instances and actual unchanged
consumers, check all 71 original signatures through typed aliases, print
their assumptions, run `coqchk` for the selected component, and separately
state whether the exact production endpoint was rebuilt. Report selected
module source savings separately from endpoint-closure savings and from
compilation time.
