# PRA subtraction recursion: independent replay

29 October 2026. I read the theorem pair and checked the actual term and
binder order. In arbitrary equality models of the candidate PRA, the defining
recursion equations imply `x−0=x` and `x−succ(y)=pred(x−y)` for the designated
function code; completeness gives closed object-theory derivations. These are
not derived from standard-natural truth alone.

A fresh independent Lean 4.32 build under `-M6000 -j1 -DElab.async=false`
matched both author objects and full logs. Seven axiom reports use only
`propext`, `Classical.choice`, and `Quot.sound`; the main log is empty.
The [replay evidence](pra-subtraction-root-replay/) preserves both author
attempts and the independent driver, state and logs. Current-source PRA
parents and inherited Foundation/Mathlib objects were reused without a full
transitive rebuild. The Q order axiom, standard-PRA compatibility and
conservation remain open.
