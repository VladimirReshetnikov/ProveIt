LEAN EXTENSION SOURCES - NOT COMPILED

Parent repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned commit: a4e5e96c456303cf231eab2aeeb3291d8889833f

Copy the .lean files in this directory into:
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/
inside a checkout of the pinned repository, beside Native.lean.

Use that repository's existing Lake workspace and lean-toolchain.
From its root, for example:

  lake build +ConciseIPRA.OneContext
  lake build +ConciseIPRA.OneContextBiInterpretation
  lake build +ConciseIPRA.OneContextOneIntro

The third module is the optional seven-constructor variant; its single
introduction condition is inherited from NativeOneIntro.WPrf.

The files have no sorry or added axiom declarations. Their constructors,
lemma names and mathematical types were checked against fetched pinned
sources and independently reviewed. Neither Lean nor Lake was installed
in the delivery environment, so no successful compilation is asserted.

The checked Python reproduction does not execute Lean and cannot establish
that these Lean extension files elaborate. This remaining verification
boundary is explicit in the report and CLAIMS.json.
