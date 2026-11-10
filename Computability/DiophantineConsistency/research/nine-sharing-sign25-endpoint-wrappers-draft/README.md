# Sign25 wrappers against the previously compiled native child

The no-alias endpoint attempt compiled `Sign25DirectNoAliasNative` and printed
its axiom report, but its overall runner later failed at the standard wrapper
and omitted final postflight. An independent audit checked the native source,
object, directly observed providers, logs, and recorded outer failure. This
source-only retry retains that exact partial native object rather than
recompiling it; its guarded runner must recheck the audited source, object,
logs, guards and overlay links. This makes the earlier failed outer run an
explicit provider qualification, not a claimed successful native run.

The two candidate wrappers add local irreducibility settings absent from the
failed standard stage. Their Lean elaboration is untested; the earlier memory
exception's precise cause remains unknown. A fresh no-Lean preflight,
independent review and exclusive Lean slot are required before a bounded run.
