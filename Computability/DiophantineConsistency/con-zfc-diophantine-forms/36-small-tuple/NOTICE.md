# Attribution and mathematical scope

This report synthesizes and extends research in VladimirReshetnikov/ProveIt,
at commit `8c6eec9d19ef80538c8e61ff6e0180040583446a`. The inspected collection is
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms`.

Packages 24 and 30 supply the separating weights and norm templates; packages
24,25,27 supply the native coefficient geometry and padding mechanisms; packages
27 and30 supply the Jones arithmetic and quartic ingredients. The new work is
the stated synthesis, exact arithmetic refactoring, smaller coefficient adapter,
and combined evaluator. This is a relative repository improvement. No general
priority or absolute-optimality claim is made.

The literal K215 machine, Wang943 language, native-window/Pell compiler, and
calibrated consistency endpoint remain inherited work. Original notices credit
the ProveIt contributors, Mira, Elliot Glazer, Jeff's busy-beaver and Rocq work,
Andrew James Wade, BusyCoq, and the Coq Library of Undecidability in their
respective scopes. Original notices and licenses are retained in the subpackages
and `licenses/`; they are not replaced by this note.

The nine-variable representation theorem is due to Matiyasevich and Jones;
the sparse/homogeneous evaluator and the fixed-instance improvements do not
claim a new representation theorem. New material is provided under ProveIt's
MIT No Attribution terms in `licenses/LICENSE.ProveIt`.

The equivalence to Con(ZFC) is an ordinary mathematical theorem formalizable
in ZFC after composing the identified interfaces. No new end-to-end Lean/Rocq
certificate, proof of consistency, unrestricted-integer interpretation of the
positive equations, or formal solution of global minimization is claimed.

The repository was inspected read-only. This archive is ready for the user's
own incorporation and does not represent an external commit or publication.
