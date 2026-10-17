`WFRelativization.lean` translates the repository's actual eight-constructor
`Form` syntax into formulas about the internally well-founded domain defined
by `WellFoundedPart`. Membership, equality, bottom and propositional
connectives retain their slots. Universal quantifiers gain an implication
from `wfForm 0`; existential quantifiers gain a conjunction with that guard.
The inserted defining guard is evaluated in the ambient structure and is not
recursively relativized.

The main statement is
`sat_translate mem phi env`: ambient satisfaction of `translate phi` under
the underlying values of `env` is equivalent to satisfaction of `phi` in
the actual WF subtype. Parameter lifting selects no representatives. The
proof handles logical equality in both directions using subtype equality,
and quantifier witnesses carry exactly their WF proofs. No model axiom,
external well-foundedness, Choice or nonempty-domain premise is assumed.
Supplying an environment into an empty domain is impossible; the theorem
does not construct one or infer nonemptiness.

The unary and binary specializations retain every parameter. In particular,
`sat_translate_relOf mem phi env y x` uses the existing Replacement
convention: output at slot0, input at slot1. Equality-free input formulas
remain equality-free, and conversely, because the inserted WF guard is
itself equality-free.

Attribution follows the existing well-founded-part layer and the pinned
Mira-Cult/Jeff busy-beaver snapshot at
`297ab8df7e5de329605c3875b4934643b371a5e3`,
`ZF/stdzf_r3/regcon/WF.v`. This adapter does not alone transport Separation,
Replacement or all ZF axioms. It makes no consistency or machine claim.

The exact source passed a fresh pinned Lean4.32.0 check in0.346seconds,
SHA256 `fccff4d33c0fa673c92e8f7a1c852d4d639d6ddf155421301ae78a9877963a1d`.
All nine exported theorem audits and three callers passed: nested binders
with an outer parameter, Replacement's identity matrix, and an arbitrary
environment supplied with WF proofs. The adapter's theorem axioms are at
most `propext` and `Quot.sound`; its principal satisfaction theorem uses
only `Quot.sound`. Both sibling agents independently reviewed the source.

Evidence is in `results/wf-model-theory-verification.json`, which records the
fresh three-module check and combined23 theorem audits/six callers. The
dependency cache was source-verified and reused; this was not a rebuild of
the entire source closure. No additional Lean check was run for this note.

The separately checked `WFModel` and `WFTheory` now use this adapter to
obtain full ZF, including Foundation, in the supplied-closure quotient and
to compare native and ZF refutations. Choice and internal arithmetic
proof-code formalization remain separate.
