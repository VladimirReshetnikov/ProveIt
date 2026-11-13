# Forty-variable quartic Lean proof inputs

The proposed proof rewrites the 41-variable quartic's second scaled root as
`mainScale * quotient`. `verify_literal.py` compares every row of the Lean
literal against the pinned 166-operation candidate graph. The context provides
30 common-residual substitution identities; the zero and map modules reduce
the comparison to those identities and the main norm. The norm module uses the
positive-scale quotient lemma. The model module proposes positive witness maps
in both directions in arbitrary IΣ₁ models, and the native module proposes the
fixed-port theorem by composing that model bridge with the 41-variable one.

The context, zero, maps and norm modules had exploratory compiled objects from
an earlier provider. The later author-side results described below compile the
complete model and native modules; they are not a paired replay. The former package provider now has
broken links; a replacement requires independently documented provenance and
the resulting verification must retain its ancestry qualifications.

`replay_native.py` prepares two guarded replays of the six model modules and
two native modules, starting from the historical QF41 peer provider. It checks
that parent's eight recorded objects and terminal observation and binds the
literal verifier and all directly observed dependency companions. The package
root is supplied as `QM40_PACKAGE_LIB`; the driver records its location, but
does not authenticate its transitive ancestry or establish that its contents
match the parent run's original package provider. The driver has not been run.

`replay_native_bounded.py` is a separate prepared driver for the same
source/provider comparison. It caps each Lean child at `-M3000` and 180
seconds, requires at least 4 GiB free before each compile, and rejects
preexisting candidate modules and companion files in the parent or package
provider. It retains the original direct-companion guards and inherited
ancestry limitations. These are sampled disk checks, not continuous resource
monitoring. Its first [bounded run](../../reviews/adaptive-qm40-native-bounded-replay/README.md)
compiled all six model modules on the author side, then timed out on the
native client. A subsequent [incremental author-side retry](../../reviews/adaptive-qm40-native-incremental-author/README.md)
compiled the native endpoint and checks on that provider; the paired replay
and a fully authenticated current-source closure remain incomplete.
