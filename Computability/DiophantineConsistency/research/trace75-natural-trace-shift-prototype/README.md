# Positive model-natural squared-to-linear trace shift

`Trace75NaturalTraceShift.natural_shift` is Lean checked in every IΣ₁ model.
For natural model elements `c,f,d,T,r`, assuming `c>0`, `f>0`, `f=1+c*d`
and positive signed old value `f²(cT-r)-c` in the difference ring, it
constructs `Tnew>0` with signed cast `fT-dr` and proves the linear-trace
value at Tnew equals the old squared-trace value.

This generic witness lemma does not bind a trace75 graph or prove a halt/iPRA
result. The accepted author run is `observations/natural-attempt02/`, object
`/tmp/trace75-naturalshift-23u480gg/Trace75NaturalTraceShift.olean` SHA-256
`b828737e9a8889dc05a8aab6e22f84dc2dd470a0265ae27d0d7462fe04498318`.
Attempt01 lacked the model syntax import and is retained. The accepted runner
pins direct providers; full transitive, package and dynamic ancestry remain
inherited. An independent source and receipt audit passed; no Lean replay was
performed.
