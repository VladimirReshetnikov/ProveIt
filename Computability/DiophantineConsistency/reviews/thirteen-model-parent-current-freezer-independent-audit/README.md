# Independent corrected 44-source freezer audit

The independent [audit](audit.py) of correction `76408407a0` exited 0 in
session 31099; its [receipt](CHECK.json) and
[terminal observation](terminal-observation.json) bind the result. It checked
the exact committed freezer and survey files, both original and corrected
outer observations, byte-identical manifests, and each of the 44 sources in
both snapshots against the anchored Git commit and workspace. Snapshot 02 is
`/tmp/ipra-thirteen-current-source-02`; it contains no Lean build result.
The original source-survey independent audit was rerun successfully after
the README restoration. The audit also ran the freezer into a fresh temporary
directory with exit 0 and the same manifest, and checked that optimized mode
and an existing output path fail closed. Its own temporary replay tree is
removed after verification.

The original successful snapshot 01 and freezer observation remain valid as
historical source snapshots. A subsequent addition to the surveyed README had
caused the independent survey rerun, and hence fresh freezer invocation, to
fail its exact-byte guard. The correction restored those reviewed bytes and
moved notes to `FREEZE.md`; the corrected run is separately recorded as
session 47339 exit 0. The two manifests match, and all 44 source bytes were
independently compared in both trees.

This approves only the checked source freezer and the observed source
snapshots. It does not approve or launch a build, establish continuous
immutability between hash checks, audit the Lean runtime or transitive/dynamic
package providers, prove an actual-zero theorem, or construct an iPRA proof.
