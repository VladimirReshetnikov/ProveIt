# Independent audit of the historical paired workflow

This is a prelaunch review of the AQ22 workflow at commit `e4926948e0`,
including an independently rerun set of synthetic controls. It does not run
the real AQ29 parent or the AQ22 extension. The earlier AQ22 author-only
artifact audit is a separate historical result.

`audit.py` verifies the task policy against the independently audited author
packet: all 37 source rows and their Git blobs, their order, and all 94 ordered
diagnostic occurrences. It applies the actual selector to the 1,210-row
historical author state and tests rejection of a missing or reordered terminal
record, a changed terminal source, and changed policy inputs. These are
structural checks, not an independent comparison of the real parent siblings.
It then reruns five existing toy programs and their five optimized-mode negative
controls in fresh temporary fixtures. Two of the programs use real Lean with
small synthetic sources and provider; neither uses the real AQ29 parent.

The original preparer protected the parent, snapshots and package overlay but
not the Foundation provider or Lean toolchain roots when choosing its output
directory. Commit `e4926948e0` adds both roots from both siblings to the
before-creation overlap check. The real-Lean toy fixture now verifies rejection
of paths underneath the provider and toolchain and confirms no directory was
created. The separate `audit_aq26_controls.py` reruns the corresponding AQ26
toy controls after the analogous fix. `audit_runbooks.py` checks Bash syntax,
parses the Python heredocs, and inspects the preparation subprocess exit and
stream recording wrappers in both runbooks without executing their commands.

The receipts contain checked hashes and the complete output and return codes
of the toy subprocesses. `terminal-observations.json` preserves the actual
outer audit command exits and outputs. Inputs must remain available at their
recorded paths to reproduce these checks.

Launching the real pair still requires the actual successful parent
coordinator exit and stdout, a completed matched pair, and all subsequent
checks specified in the runbook. A matched parent has not been established by
this review. Neither the toy controls nor the source audit establish a current
workspace replay, a PDF claim, dynamic or package-transitive provenance, or
the requested internal PRA result. The inherited Foundation build wrapper
outer exit remains unobserved.
