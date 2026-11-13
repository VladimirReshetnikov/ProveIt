# Sign25 standard wrapper import diagnostic draft

The first two standard wrapper strategies both encountered an interpreter
memory exception under the fixed limit. This diagnostic uses separate modules
that import only the audited partial native child, only the standard theory,
and both together, with no declarations. Its fail-stop order means a failing
earlier stage prevents later tests. Passing or failing an import-only stage does
not itself prove an endpoint or identify precisely what happened in a previous
wrapper; the earlier native provider is a successful child of a failed outer
run and lacks successful overall postflight.
