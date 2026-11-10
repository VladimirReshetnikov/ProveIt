# Independent staged sign24 bridge partial-failure audit

The author observed outer session 97690 exit 1. Independent checker session
26423 exited 0 and saved `result.json`. It verifies both attempted source/logs,
the conditional child object, all direct provider guards and overlay links,
its axiom report and the upstream equivalence and sign25 bridge audits.

The first child compiled the sign24 bridge transport **assuming** the sign25
bridge, reporting `[propext, Classical.choice, Quot.sound]`. The second child
that instantiates that assumption exited `-6` with an interpreter memory
exception. There is no unconditional sign24 bridge object or final postflight
in this run. The successful conditional child is evidence, not an iPRA
endpoint; provider guards do not authenticate complete dynamic ancestry.
