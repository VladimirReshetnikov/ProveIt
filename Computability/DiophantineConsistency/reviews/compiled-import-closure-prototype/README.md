# Prototype compiled-object import closure survey

[`closure.py`](closure.py) and [`read_imports.lean`](read_imports.lean) follow
imports recorded in Lean's compiled `.olean` and, when present, `.ir` module
headers. They use the ordered-root namespace-selection rule from Lean's
`SearchPath.findWithExt`: the first root containing the top-level namespace
wins, even if that root lacks the requested module. Every selected `.olean`
and relevant companion is hashed and rechecked, including absent companions;
namespace-selection observations are rechecked after traversal. Inputs are
explicit seeds and ordered roots/roles in a JSON policy. Unsupported names,
missing modules, broken links, changed objects, and the configurable module
limit cause failure. The policy roots are resolved at survey start; callers
must separately guard any original search-path symlinks and establish that the
ordered roots match the actual invocation. A required import with only an IR
artifact and no `.olean` is rejected rather than treated as complete.

This can inventory the **compiled-header object closure** of a frozen provider
more deeply than per-source direct-import guards. It is not a source-to-object
rebuild, a trace of what the target Lean process actually loaded, a proof that
no file was temporarily modified, or an authentication of dynamic code,
toolchain dependencies, native shared libraries or runtime inputs. The reader
itself uses Lean's binary parser and inherits its toolchain. Imported package
objects are identified, not independently proved correct.

After a replacement provider has passed its own independent audit, an
optional bounded survey can use that provider's exact ordered package roots and
the direct external modules from the frozen project manifest as seeds. Its
result should record the policy, actual process exit and full output receipt;
it should not delay or be conflated with the separate guarded project rebuild.
Actual runtime file observations, if captured, require a separately reviewed
trace and may reveal inputs absent from the compiled-header graph.

Run `python3 test_closure.py` after moving aside an existing test receipt. The
controls exercise a real compiled two-module transitive chain, namespace
shadowing, a missing module, a traversal limit, object/companion mutation, and
headers from real Mathlib `.olean` and `.ir` files. No project proof replay is
performed by the tests.
