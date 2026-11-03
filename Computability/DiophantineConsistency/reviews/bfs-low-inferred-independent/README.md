# Independent review of inferred fixed low-mask identity

The accepted Lean source defines `low_alias : lowNat = Nat.ofDigits (2^67) (digits (2^67) 8807 1063 support)` by rfl, then defines `low_formula := Eq.trans low_alias CompactConcreteMask.concrete_recipe`. From the explicitly inspected second theorem's type, the inferred proposition is exactly

`lowNat = (2^67)^8807 − 1 − ∑_{j∈support}(2^67)^j − 2*(2^67)^1063`,

with natural truncated subtraction and `support = ((range 943 ∪ Ico 983 993 ∪ Ico 1003 1012 ∪ Ico 1013 1032 ∪ {1063,1064,1095,2195,3296}) \ {1})`. This is source-level type reconstruction from the two equality endpoints; no separate `#print low_formula` type transcript was retained. It proves the fixed lowNat/support expression at the selected symbolic provider, not yet a displayed-port iPRA client or a Lean theorem parsing/authenticating a PDF, TeX, JSON or coefficient bytes. The separately audited display comparison supplies external transcription evidence.

The only option suppression is syntactically scoped by `set_option linter.defProp false in` to this single proof-valued `def`; it suppresses the style warning and does not assert a new axiom. `check.py` rechecks accepted source, runner, every recorded pin, output object and `[propext, Classical.choice, Quot.sound]` report, the equality endpoints and actual support source, as well as all three retained rejected attempts. Attempt02's Lean subprocess returned 0 but its defProp warning failed the strict runner; attempts01 and 03 had syntax errors. The author reports the accepted enclosing session exited 0. Direct/nearby provider paths are pinned but verified post hoc; complete source/object/package/dynamic ancestry remains inherited. No independent Lean replay was performed.
