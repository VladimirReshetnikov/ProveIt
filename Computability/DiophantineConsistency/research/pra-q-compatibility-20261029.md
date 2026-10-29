# Mapped Robinson Q axioms except order

`PRAQCompatibility.PRA_proves_qExceptOrder` proves in Lean that every actual
Foundation `RobinsonQ` axiom other than its strict-order clause maps under
`PRALanguage.embedding` to a theorem of the candidate `PRA` theory. This covers
all ordered-ring equality axioms, successor nonzero and injectivity,
zero-or-successor exhaustion, and the zero and successor equations for both
addition and multiplication. The file also exports separate theorems for each
of the seven arithmetic clauses and a theorem for arbitrary equality axioms.
These are the exact Foundation formulas mapped along the language embedding,
not newly named approximate copies.

The proofs use every equality model of the candidate theory, including
nonstandard models. The interpreted ordered-ring structure is proved equal to
the standard ordered-ring structure induced by its interpreted operations; the
arithmetic facts follow from the previously established model-level equations
and open induction. Foundation completeness yields actual object-theory proof
existence. The omitted Foundation Q order clause is
`∀ a b, a < b ↔ ∃ c, a + (c+1) = b`; it has not been established here. No
full Q interpretation, standard-PRA equivalence, IΣ₁ conservation, or
Diophantine consistency endpoint is claimed.

After an upstream source edit, the private source-current provider
`/tmp/pra-q-current-refresh-_iu8xbm0/lib` freshly rebuilt PRATheory and the four
reachable PRAAddOne, PRAAddition, PRAMultiplication and PRAExhaustion clients.
Its state, five current-source snapshots, commands and logs are preserved
alongside that provider; `/tmp/pra-q-refresh-20261029.py` is the executed
refresh driver. Finite-code/language, Foundation, and Mathlib objects remain
inherited boundaries. The final new pair compiled under Lean 4.32 with
`-M6000 -j1 -DElab.async=false`, has an empty main log and nine standard-only
axiom reports. Independent replay and full provider authentication are
separate.

Sixteen main attempts and two checks attempts are retained under
`/tmp/pra-q-compat-author-ihfc8jl8/logs`. Attempts 1, 4–7 and 10–11 were
admitted goal-inspection probes, not accepted evidence; attempts 2 and 3
failed; later attempts resolved the exact mapped syntax and model interfaces.
The final attempt 16 has no warnings, `sorry`, `admit`, or new Lean axiom.
