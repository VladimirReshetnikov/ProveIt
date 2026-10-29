# Mapped Robinson Q axioms: independent replay

29 October 2026. I read the full pair, including each literal Foundation Q
formula and the case split over the actual `RobinsonQ` constructors. The
candidate PRA proves the image of every equality axiom and every non-order Q
axiom under its ordered-ring language embedding. The order-definition case
is explicitly excluded; this is not yet full Q compatibility or a proof of
conservation.

I verified current source hashes for the five refreshed PRA dependencies and
independently rebuilt the new pair against their private outputs. Both objects
and complete logs match the author build; the main log is empty and nine axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
The [replay evidence](pra-q-compatibility-root-replay/) preserves the refresh
sources, driver and logs, all author attempts, and the independent result.
Some intermediate author probes use `sorry` and are retained only as history;
the final source contains none. Previously checked finite-code/language and
inherited Foundation/Mathlib objects were reused without a fresh transitive
rebuild.
