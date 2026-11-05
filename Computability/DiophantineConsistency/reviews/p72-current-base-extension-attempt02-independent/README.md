# Independent audit of the completed P72 current-base extension

The author-recorded outer receipt reports actual session **92122, exit 0**,
with `PASS all 681 P72 source-snapshot extension modules`. The independently
rechecked terminal progress has SHA-256
`f4bbe5f0b543497d543f243e10d8ead6d778cc3d0bf0aec96dfa73f7e622dd5a`
and records `PASS`, 681 of 681 modules, and completion of the final audit.
This reviewer did not observe the historical session exit directly.

`check.py` independently rechecked all 681 pinned current source snapshots and
their workspace counterparts, 681 retained stage rows, 1,362 dependency and
compile logs with exit 0 and no monitor stop, all 681 main Lean objects, 2,002
recorded direct dependency edges and 60,060 provider/companion guard slots.
Both endpoint logs contain their recorded axiom reports, each exactly
`[propext, Classical.choice, Quot.sound]`: four reports for P13 and five for
P14. Those are Lean metatheoretic axiom reports; the endpoint statements are
internal iPRA derivability statements, not assertions that ZFC is consistent.

The source P13 and P14 `standard_equivalence` theorems state, respectively,
that the standard iPRA theory proves an equivalence between no natural zero of
the positive-shifted `Fin 13` or `Fin 14` graph expression and negation of the
mapped native refutation formula. Their native and equality-only reference
counterparts are also reported. P14 additionally reports `P72P14.zero_iff`,
which includes the fourteenth variable's product constraint. This run did not
itself build the separate mapped Gödel–Gentzen corollary client. The
fixed-byte graph/count/degree and external file-content identifications depend
on their separately reviewed certificates, not on these axiom reports.

`check_base.py` separately rechecked all 918 shared current14 base stages:
producer logs and source hashes, 9,180 recorded output slots, and 2,647 direct
edges over 971 direct paths. The 1,000 base overlay links still resolve to
their recorded targets. `check_archive.py` independently compared all 681
rows, 1,362 logs and 681 source snapshots in the frozen archive against the
post-run files; its SHA-256 is
`884525ff2103d805cdb8b891fedaa9cf8b9be4bc5f1c67efbf8e95353b533541`.
All three scripts are read-only and use no Lean process. Their machine-readable
results are alongside this file.

The largest sampled session RSS was 3,173,523,456 bytes; the lowest sampled
host-available memory was 17,833,353,216 bytes. Sampling can miss transient
peaks or escaped processes. The checks are point observations of retained
objects and direct provider candidates: they do not reconstruct all dynamic
loads, complete package-transitive ancestry, or changes between observations.
The 681-module source extension uses an authenticated existing current14 base;
it is not a standalone from-scratch build of all dependencies. No Lean process
was launched during this review.
