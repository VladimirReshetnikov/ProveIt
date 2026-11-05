# Independent terminal audit: fresh P72 translated-consistency client

The author-recorded outer receipt reports actual session **81196, exit 0**;
both retained Lean dependency and compile records separately report exit 0,
with no monitor stop, observed descendant or monitor error. The reviewed
terminal state is SHA-256
`4ff660480d707567c0d2267087f038ecc5b0e3dd62b902238cdf27b687e61223`;
the actual output object under `/tmp/p72-p13-p14-translated-fresh-20261105/`
is `eaf40d67d9c83a790b2e1cfaada204b0d6d254f3e2eb8605a7b088d9f9e1d8c9`.
The outer exit is an author-recorded observation, not separately witnessed by
this reviewer.

The exact source is byte-identical to the separately reviewed captured client,
but this invocation's direct P14 object is the fresh-source extension object
`ca06ffe7d590b250f7585ae75f7aa4a8d9c6e8a12b14096dc56ec55caeed41aa`;
its fresh P13 predecessor is
`ef08b9c68b1f7a770f698b14fc65d221c7db399d924b69c9a3aa9e978464a48a`.
All 60 recorded direct-provider and companion guard slots still match. The
state records identical pre/post output hashes for the prior independent
681-stage audit. This review did not rerun that audit or the separate base and
archive scripts; their independently frozen results remain linked evidence.

Each checked theorem states that standard iPRA proves an equivalence between
no natural zero of the respective positive-shifted P13/P14 expression and
`(Semiformula.lMap embedding sourceSentence)ᴺ`, the mapped Gödel–Gentzen
translation of the repository's ZFC consistency sentence. The declarations
compose the fresh endpoints with `IPRABoundedRhoZFC.zfcEquiv`. The two Lean
axiom reports each contain exactly `propext`, `Classical.choice`, and
`Quot.sound`; these are Lean metatheoretic dependencies, not axioms added to
the displayed iPRA theory. This does not decide ZFC consistency or establish
external file/JSON semantics, byte linkage or degree; those are separate.

`check.py` rechecks retained logs, live object and provider hashes, the
author-recorded outer receipt, the point-in-time guards, and exact report
names and values. It invokes no Lean process. The provider chain still inherits
the current14 base and package/dynamic-load and between-observation limits;
sampled memory limits can miss transient peaks or escaped descendants.
