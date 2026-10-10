"""Propose the exact status replacement in the pinned manuscript chapter.

Default: validate and print a unified diff without modifying anything.
With --apply: write the replacement, only if the Git blob and exact old
paragraph match the audited baseline. Review the printed diff first.
This utility has not been run on the user's repository in this session.
"""
from __future__ import annotations
import argparse
import difflib
import hashlib
from pathlib import Path

REL = Path('Analysis/Polylogarithms/docs/manuscript/chapters/05-real-turning.tex')
BLOB = '49f0336656b6aa893e5ba6e904fb561c3a941cfb'
OLD = r'''These displayed decimal locations are diagnostic, not certified
enclosures. No uniqueness of $b_\dagger$ is claimed. The 11-point
finite-coefficient sweep has negative $q(b)$ at every requested
sample from $0.001$ through $0.99$, and positive $q(0.999)$;
the latter sign is proved by the independent exact certificate.
Determining the number of zeros of $q$ and the higher-order radial
behavior at its zeros remains a concrete research problem.
'''
NEW = r'''These displayed decimal locations were diagnostic, not certified
enclosures, and the original 11-point sweep did not prove uniqueness.
Its negative samples from $0.001$ through $0.99$ and its positive sample
at $0.999$ are retained as historical evidence. The latter sign also has
the independent exact certificate above. The continuation in
Section~\ref{rbif:int:section}, with full proofs and replay certificates
in \cite{rbif:continuation}, now proves a unique interior zero of $q$,
a negative sixth-order coefficient there, and a local two-extremum
region. The full-radius turning-point count remains unresolved.
'''

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repository', type=Path, help='Local ProveIt repository root')
    parser.add_argument('--apply', action='store_true', help='Write after all baseline checks pass')
    args = parser.parse_args()
    target = args.repository / REL
    raw = target.read_bytes()
    digest = hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
    if digest != BLOB:
        raise SystemExit('Baseline blob differs; inspect the current source instead of forcing this change.')
    text = raw.decode('utf-8')
    if text.count(OLD) != 1:
        raise SystemExit('The exact old paragraph was not found once; no change made.')
    updated = text.replace(OLD, NEW)
    print(''.join(difflib.unified_diff(text.splitlines(True), updated.splitlines(True),
                      fromfile='a/'+str(REL), tofile='b/'+str(REL))), end='')
    if args.apply:
        target.write_bytes(updated.encode('utf-8'))
        print('Wrote the validated replacement. Add the new section and bibliography before building.')
    else:
        print('Preview only: no files changed.')

if __name__ == '__main__':
    main()
