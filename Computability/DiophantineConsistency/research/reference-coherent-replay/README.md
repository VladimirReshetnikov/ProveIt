# Reference-theory replay preparation

`plan.py` surveys the source-declared import graph for the fixed AQ29 direct
reference endpoint and the restricted equality-only provability roundtrip. It
distinguishes project modules found in a pinned frozen parent manifest, new
workspace modules and six explicitly mapped research-draft modules. It is a
planning tool, **not a compiler or an authenticated replay**; the line-based
scanner is not Lean's parser.

The [provisional observation](provisional-observation.json) used the parent
manifest SHA-256 `63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48`
with `--basis historical --manifest-only`. It found 1,209 declared parent
modules, 31 additional project modules, and no direct external namespace
imports absent from the parent manifest. The sole unused parent module is
`DiophantineConsistency.IPRAAQ29NativeChecks`. The 31 additional paths were
tracked and unchanged against observed Git HEAD; their hashes are in the
observation. Parent source bytes and current drift were **not checked** in
this low-I/O mode and are represented by `null`, not by a zero count. Even
these graph counts remain provisional until Lean reports actual dependencies.

An initial strict current-basis survey was interrupted (exit 130) while
re-reading parent source files because of disk contention with the active
fresh project build. It yielded no source authentication result. The planner's
seven small tests passed, including current drift refusal, historical drift
reporting, snapshot tampering, cycles, draft/live shadowing and the explicitly
unchecked provisional mode. These are control tests, not an AQ29 build.

After the fresh project pair completes, a coherent extension needs all of the
following, none of which this survey has performed:

1. Capture and verify the paired coordinator's actual successful terminal
   exit, exact matched state and pinned manifest; rerun the existing parent
   comparator and provider/direct-input guard checks. A partially built pair,
   the old historical project overlay, or a lone receipt is insufficient.
2. Perform the strict source survey after the active build, authenticate the
   frozen parent snapshot and all used current source bytes and Git state, and
   freeze the 31 additions including the research drafts under their module
   paths. `--basis current` refuses reuse on any observed parent-source drift.
   The historical basis deliberately uses parent-era sources and must be
   labeled as such. For a current-source claim with drift, first make and
   independently authenticate a same-target successor pair; do not silently
   mix changed ancestors with parent objects.
3. Implement and test an **extension** builder: the existing selective-rebase
   preparer requires unchanged module sets and therefore does not directly
   accept these new targets. Each sibling must start in its own empty project
   object root seeded only by copies from its corresponding authenticated
   parent sibling. Reject preexisting additional outputs, cross-sibling links,
   old project objects in every effective search root, mismatched compiler or
   provider pins, and any direct import not explained by the frozen graph and
   Lean's actual `--deps` output. Recheck object companions, search precedence,
   source/configuration pins and endpoint axiom reports.
4. Compile all additional modules in dependency order in each sibling; compare
   their outputs, logs and full dependency records under the same independently
   audited paired-build safeguards. The six research-draft modules may fail to
   elaborate and must be fixed and re-frozen before a passing claim. Check the
   exact endpoint statements and proof dependencies after the build.

Even a successful extension inherits the parent provider's stated limitations,
including package-transitive and dynamic-load provenance. It would not by
itself prove equivalence with a separately selected ZFC proof coding. The
existing mixed-provider checks and axiom reports do not authenticate any of
these candidates.
