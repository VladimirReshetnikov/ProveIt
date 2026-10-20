# Lean-checked all-natural K + RAB + QS obstruction

`KRABModel.lean` passed Lean on its first attempt in 2.430 seconds, under the
default proof limits, one thread, a 4 GiB memory bound and a 120-second external
timeout. All 21 printed axiom reports contain only the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`. There are no warnings, `sorry`
terms, added axioms, or locally raised proof limits. No failed Lean attempt
preceded this successful run.

## Checked endpoint

The module defines a three-value valuation on **every natural number** using
fuel recursion, proves fuel stability once the fuel exceeds the code, and then
proves all four native constructor laws. Both numerical labels of membership
atoms are evaluated recursively. The zero collision `wim 0 0 = 0` is explicitly
handled, and native falsum evaluates to the undesignated low value.

The retained rho1–rho6, merged G, restricted
`rho8 a b c (wel a b)`, all K instances, all quantified-stability instances,
and the entire literal seed bundle are proved designated for arbitrary
natural parameters. The bundle lemma retains the exact matrix/private-label
coupling. Its semantic validation is stronger than required, while the
inductive derivability relation `Prov` explicitly retains both original
numeric gates on bundle introduction.

`K218KRAB.sound` proves designation by induction on every `Prov` derivation.
`K218KRAB.no_falsum` concludes `¬ Prov F`. `no_falsum_identity` and `no_code16`
additionally reject the concrete implication `F → F`, whose code is 16.

These are all-natural mathematical theorems, not finite code sampling or only
finite table calculations. They formalize the ordinary obstruction including
QS. They do **not** concern a system that additionally admits code 16, all
identities, S, or unrestricted fourth-parameter rho8.

## Exact native definitions and dependency boundary

The new module imports `BusyBeaver.ZFC.Code254` using the existing accepted
cached route recorded by the earlier positive-simulation check. Its canonical
source SHA is
`18311d4a28cba6778a0ba1a1ddee34f5c2dd5044a23958b63f46d0640be4e01e`;
the selected and actual first cached object SHA is
`f030585bad7e2281cddc172dbc3169614a74d30a59cbff9dbd92c8626a9285b3`.
The compiler, this direct pair, the source snapshot and emitted object were
pinned. The inherited cached namespace is an explicit boundary: its whole
transitive dependency closure was not rebuilt or freshly audited here.

No `KCode222.olean` was available in that declared route. Accordingly the new
namespace `Native` locally transcribes exactly its six code definitions:
`growG`, `req`, `clos`, `nks`, `vrel`, and `bundle222`. The saved static binding
receipt compares each complete declaration, modulo whitespace, with canonical
KCode222 and its published source snapshot. They agree exactly. This is an
explicit source-transcription boundary, not a claim to have imported or
rechecked KCode222's theorem facade.

The resulting `no_falsum` is a Lean theorem about the displayed inductive
derivability predicate on natural codes. It does not itself construct an
internal PA proof code, formalize second incompleteness inside ZFC, or prove
a new machine's behavior. The ordinary elementary-formalizability and
conditional calibration consequences remain explained in the parent proof.

## Attribution and review

`opening_encoder` authored the algebra and ordinary proof. `drop_contract`
authored this Lean formalization and adapted the previously declared cached
runner. `review_upstream_reflection` independently read the complete Lean
source, constructor arguments, literal transcriptions and derivation endpoint;
that peer did not rerun Lean or audit the provider cache. Root also read the
complete source and actual result. The successful execution and direct-input
postchecks are recorded separately from those source reviews.
