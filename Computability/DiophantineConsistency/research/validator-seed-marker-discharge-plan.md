# Actual internal elimination of marker/domain side formulas

27 October 2026. ROOT's proposed next pair is
`ValidatorSeedMarkerDischarge222` and focused Checks. This implements the
discharge part of the [marker-counter proposal](validator-seed-marker-counter-proposal.md),
without claiming the preceding arbitrary-derivation interpretation.

The only requested imports are `ZFCinPA.ValidatorSeedSourceBasis222` and
`BoundedPAConsistency.InternalRelativization`. The former already proves
actual source empty-object and tag-nonempty existence; the latter supplies
the represented finite domain side set and raw derivability rules.

For arbitrary internal j define the raw set-language formula codes

```text
d(j) = (&j ∈ #0),
e(j) = Empty(&j),
C(j) = domSet(set-language,d(j),j),
R(j) = {falsum, not e(j)} union C(j).
```

Here Empty retains the exact existing source spelling
`forall z (z in &j -> falsum)`. The two source variables in d(j) and
Empty are in their actual atom slots. These are raw syntax codes with
typed bindings, not assumptions that the source atoms are true.

The proposed public endpoint is

```text
for arbitrary internal N,
  Derivable seedTheory R(N) -> Provable seedTheory falsum.
```

This is a conditional proof-transformation endpoint for a concrete source
sequent. Its premise is to be constructed by the later marker-safe
interpretation, not supplied to the final equation theorem by an oracle.
It does not assert that seedTheory is inconsistent.

## Actual counter and source proof

Prove the family laws, keeping the marker variable distinct from the newly
opened variable:

```text
shift d(j) = d(j+1),
shift e(j) = e(j+1),
shift not e(j) = not e(j+1),
C(j+1) = {free(not d(j))} union setShift C(j),
R(j+1) = {free(not d(j))} union setShift R(j).
```

The C identity splits an actual internally bounded index i<j+1 into i=0
or i=k+1 and uses the ordinary represented free/substitution laws. No
shift-fixed domain hypothesis is assumed or weakened.

An actual derivation of R(j+1) can therefore be generalized at the opened
variable, giving `{forall x not d(j)(x)} union R(j)`. The accepted source
`tagged_nonempty` proof at marker &j gives `exists x d(j)(x)`. Weaken its
actual derivation into R(j), then cut to obtain a derivation of R(j).

For arbitrary internal N, genuine Sigma1 successor induction on k, with
k<=N and invariant

```text
exists j, j+k=N and Derivable seedTheory R(j),
```

removes all N side formulas. At k=N the marker is0 and C(0) is empty.
The exact source `emptyBody.free` identity then allows generalization of
not Empty(&0), retaining falsum. Cut against the actual source proof of
`exists t Empty(t)` to derive the singleton falsum sequent.

Expose fixed raw graphs for d and e, typed source bindings, totality and
the exact family shift/free/side-set laws. Definability of the side set
and residual sequent is needed for the actual induction, using the
existing represented HFS set operations. Do not assert a Sigma1 graph
for the entire chosen output-proof map without proving it.

Checks retain arbitrary internal N and j, N=0, the actual source theory,
the changing marker, graph instances and the final conditional endpoint.
Axiom reports must contain only propext, Classical.choice and Quot.sound.

## Exact reuse and limits

The accompanying read-only auditor will prune the accepted Guarded cache
to SourceBasis and add only the source-identical historical
InternalRelativization object. Its direct Foundation Proof.Basic source
and object hashes exactly match the selected current dependency. The
historical source snapshot and successful output are available; absent
server/private/IR companions retain their recorded qualifications.
No prerequisite refresh, Foundation build or accepted-source mutation is
proposed. An exact current-header DAG and every actual first artifact
provider must be checked before the two fresh leaf commands.

Use pinned Lean4.32, -M6000 -j1 -DElab.async=false, one thread, fresh regular
outputs and a512MiB reserve. Snapshot both inputs before every attempt and
preserve all failures, drivers, commands, complete logs and timing.

Still open after this pair: family interpretation of arbitrary internally
coded derivations, actual tagged/quotient/WF axiom images, Collection and
ZF/ZFC calibration. This pair by itself proves no equation/PA/HA equivalence.
