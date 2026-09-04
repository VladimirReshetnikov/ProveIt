#!/usr/bin/env python3
"""Fail if any Lean source is newer than its compiled artifact, or was never built.

Why this exists.  A build log faithfully reports a build that really happened --
of whatever bytes were on disk when `lake` read them.  It cannot tell you that
those were the wrong bytes.  Two ways that goes wrong, both observed on
2026-09-02:

  * a patch script died (relative path, working directory had silently reset),
    its error went to a background task file nobody read, and the build ran on
    the unpatched source.  The tell is a fix round returning *exactly* the
    previous round's errors, line for line;
  * a compile round was started while a drafting agent was still rewriting the
    files, using file-mtime quiescence as a completion signal.  Five of seven
    modules were rewritten during or after the round, so several `errors=0`
    results were against superseded files.  The tell is `errors=0` against a
    source newer than the artifact.

Both are invisible in the log.  This check catches both without needing either
tell, by comparing modification times.

Run it AFTER a build, to confirm the green describes the bytes on disk:

    lake build +FabiusFunction.Foo && python scripts/check_artifacts_current.py Foo

Do not put it before the build of a file you have just edited: the source is
then newer than the artifact by construction, so the check fails and blocks the
very build that would fix it.  (An earlier version of this docstring recommended
exactly that, and it is wrong.)  Before a build it is useful only for a module's
*dependencies*, to confirm you are building on current artifacts, and on its own
it answers "is this earlier green result still trustworthy?".

With arguments it checks only the named modules (bare module names, no
extension), which is the intended use: run it on what you just built.  There a
missing artifact is a failure, because you asked about that module.

With no arguments it sweeps the whole library, and there a missing artifact is
only *reported*, not treated as failure: a worktree legitimately lacks artifacts
for every module it has never compiled, and most worktrees have compiled only
their own slice.  Measured here on 2026-09-02, a full sweep found 62 modules
current and 727 never built in this worktree, none of which is a defect.  Do not
use the no-argument mode to confirm facade registrations; it will report almost
the entire library.

Credit: the idea of turning the two failure tells into one mtime gate came from
the concurrent q-series session.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, os.pardir, os.pardir, os.pardir))
SRC = os.path.join(ROOT, 'Analysis', 'FabiusFunction', 'Lean', 'FabiusFunction')
OLEAN = os.path.join(ROOT, '.lake', 'build', 'lib', 'lean', 'FabiusFunction')

# A source may legitimately be a second or so newer than its artifact when the
# filesystem timestamps round differently; anything beyond this is real.
TOLERANCE_SECONDS = 1.0


def modules(argv):
    if argv:
        return list(argv)
    if not os.path.isdir(SRC):
        sys.stderr.write('no such source directory: %s\n' % SRC)
        raise SystemExit(2)
    return sorted(f[:-5] for f in os.listdir(SRC) if f.endswith('.lean'))


def main(argv):
    names = modules(argv)
    stale, never, missing_source, fresh = [], [], [], 0
    for m in names:
        src = os.path.join(SRC, m + '.lean')
        art = os.path.join(OLEAN, m + '.olean')
        if not os.path.exists(src):
            missing_source.append(m)
            continue
        if not os.path.exists(art):
            never.append(m)
            continue
        age = os.path.getmtime(src) - os.path.getmtime(art)
        if age > TOLERANCE_SECONDS:
            stale.append((m, age / 60.0))
        else:
            fresh += 1

    print('checked %d module(s): %d current' % (len(names), fresh))
    for m in missing_source:
        print('  NO SOURCE   %s' % m)
    if argv:
        for m in never:
            print('  NEVER BUILT %s' % m)
    for m, mins in sorted(stale, key=lambda t: -t[1]):
        print('  STALE       %s (source is %.1f min newer than its .olean)' % (m, mins))

    named = bool(argv)
    bad = stale or missing_source or (never if named else [])
    if bad:
        print('FAIL: a green build log does not describe these files.')
        return 1
    if never:
        print('(%d module(s) never built in this worktree; not a failure in a '
              'full sweep)' % len(never))
    print('OK: every artifact is at least as new as its source.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main(sys.argv[1:]))
