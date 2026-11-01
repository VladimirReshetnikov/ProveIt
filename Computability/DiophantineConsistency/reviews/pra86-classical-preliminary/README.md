# 86-operation classical PRA compatibility build

The source-directed preliminary build `/tmp/pra86-classical-preliminary` compiled all 111 frozen suffix modules successfully against the preceding-snapshot 847+73 classical provider. The exact `PRA86ZFCStrict.equivalence` proof and its check compiled; the Lean axiom print is `propext`, `Classical.choice`, `Quot.sound`. This packet preserves the terminal state, complete logs and driver; source snapshots are in `reviews/pra86-classical-join-snapshot/`.

This compatibility run did not fully authenticate the inherited parent/source/object environment before and after compilation, and it is not an independent replay. It therefore does not establish a fully authenticated current-source endpoint. The separately prepared guarded latest-parent build is required. The theorem is classical candidate PRA and does not by itself prove the native intuitionistic PRA target.
