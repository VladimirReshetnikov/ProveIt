# Prepared-sequent parameterized witness

For an open matrix with finitely many parameters and a prepared existential
sequent from actual universal-theory axioms,
`PRA_parameterizedPreparedWitness` constructs one primitive-recursive code
of the exact parameter arity and a candidate-PRA proof of the matrix at that
witness. The proof translates the extracted terms, interpreting other free
variables as zero, and applies the finite selector. It still assumes the
prepared sequent; obtaining one from a general ∀∃ theorem and establishing
standard-PRA identification and conservation remain open.

Two isolated builds against the independently replayed finite-extraction
provider `/tmp/herbrand-finite-extraction-independent-yqeh1jl0/lib` matched
source, object and complete-log hashes, with only standard axiom reports.
The driver checks 56 inherited source/object pairs. The [independent driver,
state and logs](herbrand-parameterized-witness-root-replay/) and the
[author packet](herbrand-parameterized-witness-author-replay/) are preserved.
Foundation/Mathlib and unchanged local objects remain inherited boundaries.

An upstream merge after these builds changed eleven PRA prerequisites,
including Boolean, equality, exhaustion, search and order modules. This
receipt authenticates the earlier snapshot; a source-current downstream
refresh is required.
