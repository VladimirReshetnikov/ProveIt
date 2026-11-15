# Shift bad-trace and step derivations

In every PRA model with IΣ₁ arithmetic reduct, a contextual proof of the trace of a negated internal property shifts to the trace of the negated shifted property, with the source and witness free indices incremented. A contextual ordinal-step proof shifts to the step of the shifted property. Both constructions give their exact proof values using existing fixed Σ₁ proof-code graphs. The property and indices may be nonstandard when their typing hypotheses hold.

These constructions take the original derivations as premises and yield shifted contexts. They do not add the witness assumption, discharge induction, or prove the machine equivalence. The checker recompiles the source using selected byte-checked repository-built modules; other imports are prebuilt. Run from the repository root:

```
Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-bad-trace-step-shift.sh "$PWD" /dev/shm/pa194-bad-trace-step-shift-repo
```

Choose a fresh output for another run.
