# Provenance

The modified abstract core and proof renderer are derived from Vladimir
Reshetnikov's ProveIt repository, commit
`2ca3a5c16f0876d2cab842056353c03a1ed2f5f0`, particularly
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DominatedImplication.lean` and
`Computability/BusyBeaver/Research/ZFC/k225-formal/rho8cd/`.
Their existing 58-step condensed-detachment derivation is retained.

The public unrestricted basis interface and the unchanged Tarski bridge come
from `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Lukasiewicz.lean` at that
commit. The original file attributes its 107-declaration certificate to the
published `ZF/m254/coq/logic/CD254.v` DAG at Jeff's busy-beaver commit
`297ab8df7e5de329605c3875b4934643b371a5e3` (Mira-Cult's machine and Jeff's
verification). This proposal removes that duplicate certificate from the
active module; it does not change or relicense the upstream snapshot.

The universal-relation adapter, five-MP S extension, audit clients, and
reproduction/inspection scripts are contributions of this proposal. No
claim of mathematical priority is made for the implicational identities or
the standard exchange/composition reasoning.
