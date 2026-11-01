# Independent audit of the 21-module quartic model replay

The audit independently checks all 21 frozen source hashes and explicit import
headers, their topological order, the two matching rows for every module, both
actual objects and complete logs, each direct dependency hash, and every
recorded present or absent parent, fallback and direct-input guard. The audit
found that `IPRAQuarticExpressionBridge` has changed since the capture; the
21-module result is therefore historical. This audit is not an actual tool-exit
observation, nor a revalidation of inherited transitive project, package or
dynamic ancestry.
