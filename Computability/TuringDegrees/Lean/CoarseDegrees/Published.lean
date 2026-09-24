import CoarseDegrees.Sets

/-!
# Published results admitted without proof

Each statement below is a theorem from the literature, closed by the tactic `admit`.  Two
independent routes to the negative answer to C1 are supported here, and they share no admitted
statement.  A third route, through the dyadic codes, is in `CoarseDegrees.DyadicRoute` and
admits one consequence of Cooper (1973) there; the admitted classical inputs for research
report 10 are likewise stated where they are used, in `CoarseDegrees.Hyper` and
`CoarseDegrees.Cone`.  Nothing outside those four files uses `sorry`.

**Route G (1-generic sets).**
* `OneGeneric.core_trivial` — [HJKS], Theorem 4.2.

The other two ingredients of Route G are *proved*: 1-generic sets exist
(`CoarseDegrees.Generic`), and a 1-generic set is not coarsely computable
(`CoarseDegrees.GenericDensity`; this is the remark following Proposition 2.15 of [JS]).

**Route C (a c.e. set).**
* `exists_re_genericallyComputable_not_coarselyComputable` — [JS], Theorem 2.26.
* `GenericallyComputable.core_trivial` — [HJKS], Theorem 4.3, final clause.

References.
* [HJKS] D. R. Hirschfeldt, C. G. Jockusch, Jr., R. Kuyper, P. E. Schupp, *Coarse reducibility
  and algorithmic randomness*, J. Symb. Log. 81 (2016), 1028--1046; arXiv:1505.01707.
  Definition 3.1 (`X^𝔠`), Theorem 4.2, Theorem 4.3.
* [JS] C. G. Jockusch, Jr., P. E. Schupp, *Generic computability, Turing degrees, and asymptotic
  density*, J. London Math. Soc. 85 (2012), 472--490; arXiv:1010.5212.

The theorem numbers of [HJKS] and [JS] were checked against the arXiv texts on
18 September 2026.  Neither paper is formalized in `C:\ProveIt`; that repository supplies the
Turing-reducibility layer (`Computability/TuringDegrees/Lean`) on which the statements are
phrased.
-/

noncomputable section

open scoped Classical
open TuringDegrees

namespace CoarseDegrees

/-! ## Route G -/

/-- [HJKS], Theorem 4.2: "If `X` is 1-generic then `X^𝔠 = 𝟎`", i.e. every set computable from
every coarse description of a 1-generic set is computable. -/
theorem OneGeneric.core_trivial {X : Set ℕ} (hX : OneGeneric X) {A : Set ℕ} (hA : A ∈ core X) :
    ComputablePred (fun n => n ∈ A) := by
  admit

/-! ## Route C -/

/-- [JS], Theorem 2.26: "There is a generically computable c.e. set `A` which is not coarsely
computable." -/
theorem exists_re_genericallyComputable_not_coarselyComputable :
    ∃ X : Set ℕ, REPred (fun n => n ∈ X) ∧ GenericallyComputable X ∧
      ¬ SetCoarselyComputable X := by
  admit

/-- [HJKS], Theorem 4.3: "If `γ(X) = 1` then `X^𝔠 = 𝟎` [...]  In particular, the above holds
when `X` is generically computable but not coarsely computable."  Only the final clause is
stated here; the hypothesis that `X` is not coarsely computable is not needed for the
conclusion, since a coarsely computable set also has `γ(X) = 1`. -/
theorem GenericallyComputable.core_trivial {X : Set ℕ} (hX : GenericallyComputable X)
    {A : Set ℕ} (hA : A ∈ core X) : ComputablePred (fun n => n ∈ A) := by
  admit

end CoarseDegrees
