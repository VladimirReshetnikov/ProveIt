# Independent terminal audit of minimal diagnostic

The author observed outer session 59941 exit 1. Independent checker session
76460 exited 0. It validates the two attempted stages' source and log hashes,
the successfully compiled `#check` object and printed bridge type, both direct
producer bindings, all 200 guard slots and 1,382 overlay links, and reruns
the upstream bridge audit.

The `#check` stage compiled. The separate typed alias stage, without local
irreducibility attributes, exited `-6` with an interpreter memory exception
under `-M2800`. The attribute-only third stage and final postflight did not
run. This helps isolate the diagnostic behavior but does not prove the exact
cause of the original endpoint attempt or an endpoint theorem. The provider
guards and overlay checks are point observations, not complete dynamic or
transitive ancestry authentication.
