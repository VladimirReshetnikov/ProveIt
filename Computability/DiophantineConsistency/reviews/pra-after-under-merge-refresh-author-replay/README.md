# Post-merge PRA bound graph refresh

The source-current audit identifies 14 changed sources and rebuilds 32 affected modules, including BV/fixpoint, formula-set/history, positive/negative underDef, and seqDef clients. The local parent overlay records separately independently replayed providers. External package and unlisted Foundation transitives are inherited; listed Foundation boundaries, including Seq, are checked. This refresh does not construct a uniform history or establish a rho/HA certificate.

Replay: `python3 Computability/DiophantineConsistency/reviews/pra-after-under-merge-refresh-author-replay/replay.py --parent /tmp/pra-after-under-merge-overlay-7nx3b9yb/lib`.

The author, root, and private replays all passed with matching source, object, and log hashes on the checked snapshot before the pending merge. That merge changes `PRADomainExistsBound`, `PRANegDomainExistsBound`, and `PRASeqDefWitnessBound`, all included in this graph; the packet is a preceding-snapshot receipt after the merge until the affected graph is refreshed.
