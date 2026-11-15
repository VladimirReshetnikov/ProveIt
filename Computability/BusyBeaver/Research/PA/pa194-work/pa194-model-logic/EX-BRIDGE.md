# Existential introduction in the PA194 compiler

`targetAllSpecialize_of_vacuity` derives target universal specialization from
an explicit vacuity premise using the numerical calculus. The existential
introduction bridge converts a target introduction proof into the compiler's
exact existential rule; another bridge obtains it from the stated code equality
and target vacuity.

The compiler implication is checked for truth, falsum, and positive or negative
binary source atoms whose arguments are free variables at arbitrary model-valued
indices. The source term is arbitrary, and `RankedAdmission e d` supplies the
freshness needed for atoms. These atoms do not contain the substituted bound
variable. General introduction, including quantified bodies, remains open.
This package does not construct a complete compiler or a consistency direction.

`check-ex-bridge.sh` performs the standalone source replay and checks thirteen
axiom reports. A replay with an existing output directory reuses its nonlocal
objects, so those objects and the workspace foundations retain their own
provenance requirements.
