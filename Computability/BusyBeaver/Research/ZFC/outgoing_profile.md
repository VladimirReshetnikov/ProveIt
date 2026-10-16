`OutgoingProfile.lean` proves source24's short outgoing predicate from an
explicit resource already available in the raw PSC development. It also
checks a reserved-zero semantic translation of every named formula. These
results do not provide an EPSC schema adapter, a numerical proof translation,
or a new consistency-machine calibration.

The predicate is

```text
Outgoing(a,b) := forall z, (a in z -> b in z).
```

`outgoing_iff_full` assumes `RawPSCProfile.TwinSingletons mem`. For each a,
that resource supplies an s whose members are exactly the full observational
twins of a. Since a belongs to s, Outgoing(a,b) puts b in s; hence b and a
have the same full profile, and symmetry gives Full(a,b). The converse is
immediate from outgoing profile agreement. `outgoing_mem_congr` therefore
transports membership in both arguments. It identifies observational classes;
it does not equate raw objects or collapse incoming-profile equality alone.

The actual De Bruijn formula is

```text
All(Imp(Mem(i+1,0), Mem(j+1,0))).
```

`sat_outgoingForm`, `equalityFree_outgoingForm` and
`outgoingForm_four_nodes` check its semantics, equality-freeness and four-node
tree count. Labels, formula codes, parameter closure, logic, compiler and
initialization are excluded from that count. The model corollaries obtain
twin singletons from `RawPSCModel.twins_of_model`, which uses actual
formula-indexed equality-free PSC matrices. They assume no closure schema for
all arbitrary external semantic relations. A witness explicitly supplies the
usual nonempty first-order domain.

The named translation maps source variable n to n+1, and shifts every
universal binder by the same amount. Membership keeps its two shifted
arguments, equality becomes

```text
All(0, Imp(Rel(i+1,0), Rel(j+1,0))),
```

and primitive Bottom becomes `Rel(0,0)`. The target uses only membership,
implication and universal quantification, as `translate_membershipOnly`
proves. Source equality is interpreted by `RawPSCProfile.Full` in the
explicitly defined `FullSat` predicate. It is not interpreted by raw identity.

For any e with `not mem e e`, `sat_translate` proves, for every named source
formula and every source environment, that target satisfaction in the pointed
environment equals `FullSat` of the source. Only this one false point is
required; global irreflexivity is absent. Every translated source binder is
positive, so `pointed_update` keeps zero fixed even when the source binder is
named zero. The equality expansion's local zero binder encloses only its
positive endpoint atoms, so it does not capture a translated Bottom.

`translation_of_model` obtains an empty e from actual raw PSC and supplies
that same e for the simultaneous semantic translation of all formulas and
environments. No new axiom asserting arbitrary predicate representation is
introduced. The source24 EPSC-to-PSC bridge, quotient interpretation with
ordinary identity equality, formula substitution/proof transport, numerical
schema gates, compiler simulation and the internal ZFC endpoint remain
separate obligations. A generic semantic translation is not an implementation
of the changed compiler frontend.

The outgoing predicate and reserved-zero construction are attributed to
batch151 source24 (`zfc_consistency_proposal.zip`, inner
`zfc_minimal_theory`), inspected against ProveIt commit
`2178c3885423f923021d4aaf1dbf52b4e2060837`. The twin-singleton resource is
prior raw PSC work already formalized by `RawPSCProfile`/`RawPSCModel`.
The Lean proofs in this module are new project work; they do not import a
formal proof from the manuscript.

The source and an independent caller passed serial checks with the explicit
Lean4.32.0 executable at
`/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean`, release
commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`. The final source check took
0.406seconds and the caller0.274seconds, with no warnings. The twelve caller
audits include seven with no axioms, two model corollaries using `propext`,
and three translation/environment results using only `propext`,
`Classical.choice` and `Quot.sound`. No admission, custom axiom,
`native_decide` or unchecked external computation is used.

The checks reused the source-matched dependency cache and did not rebuild
`Boot253` or any dependency. A scratch overlay points to the existing
`.olean` files and contains only the newly built module. The initial caller
attempt used two conflicting `LEAN_PATH` roots and failed to locate a cached
dependency; the final single overlay resolves that import without changing
the proof. An independent read-only source review checked the outgoing
direction, all binder shifts, false-point premise and stated scope.

[results/outgoing-profile-verification.json](results/outgoing-profile-verification.json)
records the source identity, commands, final outputs and exact theorem audits.
The subsequent integration adds the module to the project umbrella and serial
checker; its scoped integration evidence is recorded separately.
