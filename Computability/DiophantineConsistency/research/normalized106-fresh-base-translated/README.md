# Fresh-base translated consistency endpoint for 67/106

The [client](Translated106.lean) checks that standard iPRA derives a
biconditional between the 67-operation degree-106 expression's no-positive-zero
sentence and Foundation's ZFC consistency sentence after the source-language
embedding and Gödel–Gentzen translation. It composes the native theorem from
the successful [fresh-base model client](../normalized106-fresh-base-model-build/README.md)
with the existing bounded-refutation/translated-consistency equivalence.
This is a derivability statement, not a proof of either side separately.

[Attempt 02](attempt02/) passed: the observed outer session 66668 exited 0;
the dependency and compile commands also exited 0. The compile log has no
warning or error and its sole axiom report lists `propext`, `Classical.choice`
and `Quot.sound`. The 2.086-second Lean compile used `-M2800`, one thread,
nice 19, idle I/O and a 180-second foreground timeout; there was no automatic
group-RSS or host-memory stop. The runner rechecked the successful model
client and sixteen extension objects and their recorded guards, the
source/base preflight before and after, and 80 direct dependency companion and
shadow slots before and after. Both preflights matched the pinned result.

The compiled client source SHA-256 is
`3c73e83da63cd6acd1a041b3fe08cd22b05781426e820351f28d2db30fa6616b`;
the result state SHA-256 is
`76122622ac57776c6068f54b419a77e8ad7935675e9256a3f5ee1ea186eda3e7`;
the temporary object `/tmp/normalized106-fresh-model-translated-v2-20261105/Translated106.olean`
has SHA-256 `0957aebccbcb35f644a746c7dea67cbf7f6b253248f75c7827e40fd65132a233`.

[Attempt 01](attempt01/) exited 1 in observed outer session 91078 because the
source omitted the namespace containing `positiveShift`. Its failed
`sorryAx`-bearing report is preserved and is not evidence of a theorem.
That attempt was launched from the model-build packet before this separate
translated packet was created; its retained source and runner are exact copies.

The theorem inherits the original model client's source/base and package
ancestry limitations and its separation from the external graph, coefficient,
degree, TeX and PDF comparisons. It is a check against the same base, not a
new independent base rebuild; package-transitive, dynamic and
between-observation ancestry remain outside these direct checks.
