# Fresh-base translated consistency endpoint for integer 66/138

The [client](Translated138.lean) checks that standard iPRA derives the
biconditional between the integer 66/138 graph's no-positive-zero sentence
and Foundation's ZFC consistency sentence after the source-language embedding
and Gödel–Gentzen translation. It composes the native theorem from the
successful [fresh-base 66/138 client](../current2011-unscaled66-fresh-base/README.md)
with the existing bounded-refutation/translated-consistency equivalence. It
does not prove either side separately.

[Attempt 02](attempt02/) passed: observed outer session 21034 exited 0; the
dependency query and compile also exited 0. The compile log has no warning or
error, and its sole axiom report lists `propext`, `Classical.choice`, and
`Quot.sound`. The 2.357-second Lean compile used `-M2800`, one thread, nice
19, idle I/O and a 180-second foreground timeout; there was no automatic
group-RSS or host-memory stop. The runner rechecked the successful 66/138 and
106 model clients and the sixteen extension objects and their recorded direct
guards, ran the source/base preflight before and after, and checked 100 direct
companion/shadow slots before and after. Both preflights matched the pinned
result.

The source SHA-256 is
`f5593d902bfb493c25b6f6ed6ca8b5f2cfe11f93f570c6bc0b91ef51fe920650`,
the result-state SHA-256 is
`1fb8f44bcef7c2717aac985ee8d5ed7f39c278b14316f3d21240f17c44eda10e`,
and the temporary object
`/tmp/current2011-unscaled66-fresh-translated-v2-20261105/Translated138.olean`
has SHA-256 `9a73122949dc09304251408cf0d10586634d390e5547bca6e8d1ee939c747cf5`.

[Attempt 01](attempt01/) exited 1 in observed outer session 38776 because its
unqualified `expressionAt` was ambiguous between 13- and 14-variable syntax.
Its failed `sorryAx`-bearing report is retained and is not evidence of a
theorem. The successful check inherits the original model client's
source/base and external package ancestry limitations and its separation from
the external graph, coefficient, degree and document comparisons. It is not
an independent base rebuild.
