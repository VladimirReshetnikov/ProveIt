# Sign25 native-expression split diagnostic draft

The original sign25 native-expression stage hit an interpreter memory exception
under `-M2800`. This source-only diagnostic separates the bridge import,
expression alias, bridge theorem and axiom report into four ordered stages.
The statement in the third module is the same kind of typed bridge as the
failed stage, with a diagnostic namespace and a separately imported alias.
Different import boundaries can change resource behavior, so outcomes locate
the first failing stage of this diagnostic and do not prove the exact cause of
the original failure. Even if all stages pass, no iPRA endpoint follows.

The sources are uncompiled. A guarded same-limit runner, independent prelaunch
review and an assigned Lean slot are required before testing.
