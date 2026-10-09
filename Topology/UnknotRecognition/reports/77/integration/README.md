# Proposed integration contract

## Placement, not automatic promotion

The delivery is suitable for the next available
`Topology/UnknotRecognition/reports/<NN>/` directory under the repository's
incoming-report procedure. Do not assume the next number from this snapshot;
the catalogue changes independently. The delivered layout may be retained.
There is no runtime overlay or patch to apply.

The current torus `normal_boundary_geometry.py` parity observer should remain
unchanged. It already decides the relevant predicate on its own verified
simple-circle/torus inputs. Adding this module as its unconditional replacement
would introduce complexity without establishing a benefit.

## Minimal higher-genus geometric adapter

A later adapter must bind all of the following to the same immutable source:

- A closed, connected, orientable boundary surface, its genus, and its actual
  relation to the current hierarchy state.
- A marked presentation with the convention `[u,v] = u*v*u^-1*v^-1` and surface
  relator `[a1,b1]...[ag,bg]`.
- A selected component and an ordered SLP representing its based word.
- An independent argument that its free homotopy class is the particular
  simple boundary circle, traversed once. Long conjugating paths are allowed.
- Any boundary-pattern or puncture information necessary for the caller's
  actual predicate. Closed-surface nullhomotopy alone is insufficient for
  general pattern admissibility.

An unsigned incidence histogram, signed exponent vector, scalar Euler data,
or component count cannot replace the ordered word. The two words
`a1 b1 a1^-1 b1^-1` and `a1 a1^-1 b1 b1^-1` have the same signed letter census
but different central signatures.

The word certificate hashes a canonical JSON record and includes that entire
record for replay. The digest is a data-binding aid, not a proof of geometric
provenance. An actual adapter must replay the word/source binding as well.

## API use and states

```python
from boundary_kernel import SLP, certificate
from boundary_kernel.verify import verify_certificate

program = SLP(word_record["rules"], word_record["root"])
observation = certificate(program, genus, transport_safe=True)
assert verify_certificate(observation)  # algebra only
```

The observation has algebraic status `NONTRIVIAL` or `UNDETECTED`, and a field
`requires_external_simple_source_for_consequence` that is always true.
Its `simple_curve_consequence` is not an independently verified geometry
verdict. `UNDETECTED` must not become `UNKNOT` or even `CONTRACTIBLE` in a
caller that has not discharged the source-simple contract.

The independent replay uses dense matrices and has a larger polynomial
cost than the scalar producer. Include its work in complete query timing.
For untrusted inputs, set the caller's own limits on encoded bytes, genus,
rule count, time, and replay memory. A resource limit should produce an
inconclusive/resource outcome, not a negative topological certificate.
The low-level `Kernel` arithmetic assumes canonical validated signatures;
SLP evaluation and transport validate the external image/signature inputs.

## Cached marking changes

Do not cache only narrow q=g values in even genus if future subword transport
is possible. Use q=2g from the start. It is impossible to reconstruct all
missing transport information from an old narrow signature.

```python
from boundary_kernel import Kernel, TransportPlan

kernel = Kernel(genus, transport_safe=True)
plan = TransportPlan(kernel, generator_image_signatures)
new_value = plan.apply(old_value)
```

Construction checks the finite symplectic tuple once. `apply` reuses that
check. Image words and their source homeomorphism/retriangulation certificate
must be supplied separately; this finite test does not certify them.
The convenience `transport(...)` function constructs and rechecks a plan on
each call. For many values, use `TransportPlan` explicitly.

Default marked-generator evaluation is lazy and obeys the input-sensitive
compiler bound. Supplying a full custom image table additionally costs its
validation/read size, O(g^2 log(g+1)) bits in the dense representation; that
is part of image setup, not free work hidden in a one-rule program.

## Promotion gate

Before native promotion, produce an actual source-bound ordered-component
adapter, independently replay its outputs, and cross-check them against a
separate surface-word algorithm or small explicit geometric examples.
Include genus, marking, simple-curve provenance, and pattern-negative cases.
Then measure complete local queries, including failed probes, source
extraction, changes of marking, and replay. Run the maintained upstream suite
on the adapted runtime. None of these native-promotion steps has been carried
out by this delivery.

The priority research question is polynomial, source-bound extraction of an
ordered boundary-component SLP from the maintained compressed normal-orbit
machinery. The article lists nine further directions and the remaining global
amortization problem.

## Binary character convention

`analyze_bank` identifies a character with its symplectic-dual vector, whereas
`lift_chain` and `contraction` accept its literal coefficient covector.
Convert with `alpha_covector = j_action(bank_vector, genus)` before passing a
bank vector to those functions. The standard J matrix swaps a_i and b_i bits.
The built-in `cover_observation` already uses its own specified covector bank;
that bank is optimal as well. Do not mix these two conventions in an adapter.
