# Structured register-program components

The remote L2 development through `2628aa9813` supplies `RMDag`, `Dag254`,
`L2Lib254`, `L2Macros254` and `L2Control254`. Independent source review found
the actual statements consistent with the attributed pinned upstream
`RM.v` and `Dag254.v`; all219 program rows were independently compared.
The five modules now compile serially with pinned Lean4.32 in the standard
ZFC runner. Their source checks and a joint umbrella check are recorded in
`results/infinity-l2-integration-verification.json`.

`RMDag` specifies structured termination outcomes, loop restarts and
register transfer/copy/clear routines. `L2Lib254` relates a nine-field record
to that register file. The pairing routine adds P(input1,input2) to its
existing output accumulator and clears its inputs. The two unpair walks
compute `ofNat(P(initial_s1,initial_s2)+counter)`; plain unpairing of the
counter requires the explicit zero-scratch premise.

The macro file proves stack operations, additive reads and all four formula
constructor tags with the actual cleanliness assumptions. The control file
proves the destructive equality test, candidate fetching, MP and both NIP
branches. Equality testing clears both compared registers; NIP clears the
old parameter before popping and halts exactly when the tested parameter
is1. These details match `Enum254`, rather than a simplified register model.

The `L2Lib254` introductory phrase saying every loop is transfer/copy/clear
is too broad: the pair and unpair loops have their own proved shapes. The
actual theorems retain these distinctions. The later two files provide the
macro/control results previewed by that introduction.

This checkpoint does not prove the AX branch or the root enumeration loop.
The DAG unfolding and the literal `Prog254` tree are also different trees:
both have6459 cells, but their depths are96 and34. A literal tree identity is
therefore unavailable. The published3010-entry path bisimulation, or an
equivalent justified relation, remains necessary before connecting this
structured program to the existing path semantics. Concrete binary dispatch
is another separate simulation; the new `BreakSite253` theorem proves only
its stated001→1 site. Source review and the local kernel checks supply no
whole-program or machine endpoint.
