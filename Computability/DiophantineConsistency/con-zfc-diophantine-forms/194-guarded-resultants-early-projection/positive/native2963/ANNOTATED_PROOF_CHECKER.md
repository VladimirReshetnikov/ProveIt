# A direct checker for sealed-ZFC certificates

`Lean/DiophantineConsistency/AnnotatedProofChecker.lean` defines an executable
checker for finite, parent-index proof certificates in the repository's original
first-order natural-deduction calculus. It has no dependency on K215, the Jones
construction, or a translation to another proof calculus.

Each certificate consists of a list of axiom tags and a list of proof lines.
The tags enumerate the six fixed ZF axioms, the choice axiom, separation with
its formula parameter, and replacement with its formula parameter. Their
interpretation applies the actual `sealF` operation to the actual formulas in
`ZF.Zf` and `BoundedZFCConsistency.Choice`. An axiom tag therefore contains
finite syntax; it does not contain or query a proof of axiom membership.

A line contains one of the original calculus's seventeen rule tags, raw context
and formula annotations, and a list of backward parent indices. Index zero is
the latest accepted line. The checker compares the selected judgments with the
rule's exact ordered premise list, including binder renaming and substitution.
It also checks assumption membership. An out-of-range index, wrong arity,
wrong context, or wrong formula rejects the line. The remaining rules have no
additional side condition in this calculus. Accepted lines extend the history;
a failed line aborts. Repeating an index allows two premises to share one line.
The final judgment must have exactly the context emitted by the certificate's
axiom tags and the requested conclusion.

The checked general theorem is

```lean
exists_checked_iff (goal : Form) :
  (∃ c : Certificate, c.check goal = true) ↔ BProv ZFCax_s [] goal
```

In particular, `exists_refutation_iff` specializes the goal to `fBot`, and
`no_refutation_iff` identifies universal checker rejection with
`¬ BProv ZFCax_s [] fBot`. This is a statement about the repository's exact
sealed theory and calculus, not a new assertion that ZFC is consistent.

Soundness interprets each accepted line by the corresponding original
`Prov` constructor. Completeness uses induction on a `Prov` proof in `Prop`.
Each induction step proves existence of a finite line fragment that works over
any older history; concatenating fragments supplies explicit backward offsets.
Thus no elimination from a propositional proof into certificate data, choice
operator, or hidden axiomhood oracle is used. The definitions of certificate
data, axiom interpretation, line validation and execution are computable.

`Lean/checks/AnnotatedProofChecker.lean` checks malformed references, arity,
context, binder shifts and equality instantiation; it also reduces valid
sharing, discharge, choice and separation fixtures. Its axiom audits cover the
data/checker definitions and the soundness and completeness theorems.

This module supplies a small direct semantic starting point for a future
arithmetization. It does not yet encode certificates as natural numbers,
prove the checker primitive recursive, compile it into a Diophantine equation,
or establish an equation-size improvement. The separate sharing-preserving
DAG compiler is not used in this module.
