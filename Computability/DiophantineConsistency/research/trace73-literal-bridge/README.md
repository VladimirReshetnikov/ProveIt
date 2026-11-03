# Literal 73-row ring bridge

`Trace73Literal.graph73` is a literal 73-row straight-line expression over an arbitrary commutative ring, with ten witness and four coefficient inputs. `literal_eq` proves that this expression is definitionally equal to `Trace73Center.value73`. `parent_substitution` combines that result with the prior all-ring identity: the 75 expression at slot 7 updated by `n + V² B` equals this literal 73 expression. Both checked axiom reports list only `propext`.

The guarded Lean check in `observations/attempt01/` exited 0, with empty stderr and no warnings; the outer runner was observed exiting 0. It pins the direct `Trace73CenterV2` object and selected 75 provider; inherited project, package and dynamic ancestry is not independently rebuilt here. The accepted object is `/tmp/trace73-literal-1adlrevr/Trace73Literal.olean`, SHA-256 `e4bbe335d32f1f50ed2bfe2440c37f19a1f34ae4def4ff476b6e0778dfc3654d`.

Separately, `check_rows.py` parses the literal Lean source and compares every operation, operand, input position and output with the pinned `../trace73-center-probe/candidate.json`; `observations/rows01/` retains its successful external check. `generate.py` generated the literal source from that candidate. The source/JSON comparison remains an external computation, not a Lean theorem about JSON or PDF bytes.

This is a ring identity. It establishes neither positivity of the transformed witness nor equivalence of positive zeros, an iPRA theorem, or a 73-row display.
