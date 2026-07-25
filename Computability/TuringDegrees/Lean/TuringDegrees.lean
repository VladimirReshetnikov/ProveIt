import TuringDegrees.Basic
import TuringDegrees.Computable
import TuringDegrees.Join
import TuringDegrees.Halting
import TuringDegrees.Structure
import TuringDegrees.Representatives
import TuringDegrees.Cardinality

/-!
Public facade for the Lean formalization of Turing degrees of sets of natural
numbers: characteristic oracles, reducibility and equivalence, the quotient
partial order, degree zero, binary joins, complement invariance, and the
ordinary halting degree `0′` with its c.e. completeness properties.  It also
records page-level order-theoretic notions and constructs infinitely many
distinct representatives of every degree.  A finite syntax for one-oracle
programs proves that every degree is countably infinite and every lower cone
of degrees is countable; a fiber-cardinality argument then proves that there
are exactly continuum many degrees and continuum many degrees in every upper
cone, even after the base degree itself is removed.
-/
