#!/usr/bin/env python3
"""Re-pin exactly one unused-simp-argument source correction."""
from hashlib import sha256
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
OLD_CONE = HERE.parent / 'compact12-ipra-expanded-cone-preflight/result-v2.json'
REJECTED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage64/observations/batch-013/stage-0064'
SOURCE = REPO / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Root254.lean'
OLD_SHA = '20b2ef7733a0d85c5248ee598b5386f42ad46319a003488fb63bfacb7f737e9f'
NEW_SHA = 'fee84717177d6575f576ae3e09a3a034071f02422b7a5ef8d9d68e7822864d10'
CONE_SHA = '35fce2dd6720ca1f2db8c39e42ad099f5653bf6b12939fcb77db3fd0fa252ed4'
TERMINAL_SHA = '3dafb33a462dc6f3eb5f54eb1147808f638cd82690d211adc7f6df600d8b8178'
LOG_SHA = 'c8b9ce7400ba4db29394cadf3692391a8233b61be1b08d6a2a85315b66b57465'
MODULE = 'BusyBeaver.ZFC.L2Root254'

def digest(p):
    return sha256(Path(p).read_bytes()).hexdigest()

def main():
    out = HERE / 'cone-repinned.json'
    if out.exists():
        raise RuntimeError('refusing to overwrite re-pin')
    for path, expected in ((OLD_CONE, CONE_SHA), (REJECTED / 'source.lean', OLD_SHA),
                           (REJECTED / 'terminal.json', TERMINAL_SHA),
                           (REJECTED / 'compile.log', LOG_SHA), (SOURCE, NEW_SHA)):
        if digest(path) != expected:
            raise RuntimeError(f'input drift: {path}')
    before = (REJECTED / 'source.lean').read_bytes()
    after = SOURCE.read_bytes()
    old = b'simp [toAS, Enum254.fetch, h, hv]'
    new = b'simp [toAS, Enum254.fetch, hv]'
    if before.count(old) != 1 or before.replace(old, new, 1) != after:
        raise RuntimeError('source correction is not the single intended deletion')
    terminal = json.loads((REJECTED / 'terminal.json').read_text())
    log = (REJECTED / 'compile.log').read_text()
    if terminal['exit_code'] != 0 or terminal['success'] or not terminal['guards_unchanged'] or \
       'warning: This simp argument is unused:' not in log or '  h\n' not in log:
        raise RuntimeError('rejected-stage evidence does not match the warning')
    cone = json.loads(OLD_CONE.read_text())
    row = cone['candidate_sources'][MODULE]
    if row['source_sha256'] != OLD_SHA or cone['topological_candidate'][63] != MODULE:
        raise RuntimeError('old cone target mismatch')
    row['source_sha256'] = NEW_SHA
    row['source_bytes'] = len(after)
    cone['source_correction'] = {'module': MODULE, 'old_sha256': OLD_SHA, 'new_sha256': NEW_SHA,
                                 'old_cone_sha256': CONE_SHA, 'rejected_terminal_sha256': TERMINAL_SHA,
                                 'rejected_log_sha256': LOG_SHA,
                                 'edit': 'remove the single unused h from the warned simp list'}
    out.write_text(json.dumps(cone, indent=2, sort_keys=True) + '\n')
    (HERE / 'corrected-source.lean').write_bytes(after)
    print(json.dumps({'module': MODULE, 'old_source': OLD_SHA, 'new_source': NEW_SHA,
                      'repinned_cone_sha256': digest(out)}, sort_keys=True))

if __name__ == '__main__':
    main()
