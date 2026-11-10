# Independent failure review: generic ofDigits finite sum

Confirmed failure. Author-observed outer session 97572 exited 1: Lean rejected `generalizing v` as unnecessary, despite printing an axiom report without `sorryAx`. The stage produced no object or successful postflight, so the printed report is not a successful checked module. Frozen/live state and logs, source, monitor records and overlay links match; the numeric outer receipt has no state hash. No Lean replay was performed.
