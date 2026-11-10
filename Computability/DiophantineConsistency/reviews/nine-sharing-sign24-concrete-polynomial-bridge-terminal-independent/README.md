# Independent audit of failed sign24 polynomial-bridge attempt

The author observed outer session 56027 exit 1. Independent checker session
79767 exited 0 and records `result.json`. It validates the attempted source,
dependency and compilation logs, all three direct provider bindings, 200 guard
slots, 1,397 overlay links and their upstream audits.

The dependency scan succeeded, but Lean compilation exited `-6` with an
interpreter memory exception under `-M2800`. The candidate object and final
postflight do not exist, so this attempt proves no sign24 polynomial bridge
or iPRA endpoint. Point observations do not authenticate complete transitive
or dynamic ancestry, and Lean was not independently replayed.
