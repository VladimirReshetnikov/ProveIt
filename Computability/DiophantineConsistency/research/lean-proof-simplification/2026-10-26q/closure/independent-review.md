# Independent review of CertificateClosure

Reviewed against `ObjectCodeBound.lean` at commit
`9bd29079d5e1c6cc1c0bcaee6cb57d59b835cba9`.

## Correct generic semantics

The proofs of `closed_empty`, `closed_join`, `closed_insert`,
`certified_of_step`, and `certified_good` follow from exactly the declared
membership laws and step monotonicity. The union proof uses each input
certificate's closure and transports its local step to the union. Insertion
requires the new item's step in the old certificate, then transports it to the
union with a singleton. It does not infer closure under arbitrary enlargement.
No extensional equality of certificates is needed.

## Exact intended interpretation

| Prototype | ObjectCodeBound |
| --- | --- |
| `Item` | `V × V` |
| `Cert` | `V` |
| `mem (c,b) S` | `mem (kpair H c b) S` |
| `empty` | `vempty H` |
| `join S T` | `vcup H S T` |
| `singleton (c,b)` | `vsingle H (kpair H c b)` |
| `Good (c,b)` | `mem b (omegaV H)` |
| `Step S (c,b)` | `BoundStep H S c b` |
| `Closed ... S` | `BoundClosed H S` |
| `Certified ... (c,b)` | `BoundCodeRel H c b` |

The membership laws follow from `vempty_spec`, `vcup_spec`, `vsingle_spec`,
and `kpair_inj`. The pair item type is important: existing `BoundClosed`
quantifies only encoded pairs and permits unrelated objects in the certificate.
The generic interpretation preserves that exact behavior.

## Adapter obligation that remains

The existing `boundStep_mono` theorem at lines 50-62 accepts full internal subset
`Sub mem S S'`. The prototype's `Included` under the interpretation above is
weaker: it transports only encoded-pair memberships. Therefore the existing
monotonicity theorem cannot be used verbatim as the required arbitrary
`StepMonotone` proof.

The needed strengthening is nevertheless direct. Inspecting `BoundStep` and its
constituents (lines 24-41), every certificate-dependent premise is a membership
of an encoded pair: two such premises for each binary constructor and one for
each quantifier constructor. The current eight-case proof can be adapted to the
weaker pair-inclusion hypothesis; full-subset monotonicity then follows as a
wrapper. This should be counted as adapter work, not silently assumed checked.

## Claims that are not justified

The prototype does not establish finite certificates, standardness,
well-foundedness, termination, totality, uniqueness, or identification with a
least fixed point. In particular, a locally closed certificate can be cyclic
for arbitrary Step. The existing definable induction arguments remain necessary
for the internal code semantics.

There is one clearly identified current client. Treat this as an optional API
proposal until a second client makes the general abstraction economical. There
is no measured net source-line saving or full ObjectCodeBound integration check.
