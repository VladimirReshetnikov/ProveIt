# Native named formulas as actual first-order matrices

`NamedForm254.lean` translates every `Tarski.NF` into the repository's actual
de Bruijn `Form`. Membership, native equality and genuine Bottom retain their
meanings. A binder sends its own name to slot0 and shifts all other current
slots. The satisfaction theorem permits arbitrary slot maps, including
noninjective maps and repeatedly shadowed binders; no fresh-name or
irreflexivity premise is needed.

The matrix adapter reserves slot0 for the input, slot1 for the output, and
slot2+i for the original parameter named i. For names a,b it gives output b
precedence, matching exactly `update (update env a x) b y` even when a=b.
`NamedForm254.sat_matrix` identifies the resulting literal `MatrixRelation`
with named satisfaction under those updates. The original numerical bundle's
separate eligibility gates are untouched.

This is a syntax/semantics adapter, not a collection instance. In particular,
a native equality atom translates to `fEq`; the result is not automatically
an equality-free matrix. The [duplicate-profile obstruction](duplicate_profiles.md)
shows why the equality-free CP/GIC interface cannot alone fill that gap.
The [all-code freshness theorem](decode_fresh254.md) separately permits the
actual decoded matrix's auxiliary binder update to be ignored, including
truth code0. Together these are finite ingredients for an eventual reverse
model construction, not a consistency or machine endpoint.

The source passed pinned Lean4.32 in0.349seconds. All five theorem axiom
audits passed with at most `propext` and `Quot.sound`; the native-equality
syntax fact is axiom-free. Caller checks include input/output-name collision
and a shadowed binder. Independent review found the slot ordering and binder
semantics correct. Development replaced an over-eager simplification and an
unavailable `split_ifs` tactic with explicit conditional cases. The final
source and umbrella check have no warnings or admissions. Commands, source
identity, audits and callers are in
`results/decoder-duplicate-integration-verification.json`.
