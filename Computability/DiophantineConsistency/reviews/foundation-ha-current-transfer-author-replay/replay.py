"""Private two-leaf replay over authenticated existing narrow/HA objects."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
REV = ROOT / 'Computability/DiophantineConsistency/reviews'
SRC = ROOT / 'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
BUNDLE = Path(__file__).resolve().parent
MANIFEST = BUNDLE / 'inputs.json'
LEAVES = ['FoundationHACurrentTransfer', 'FoundationHACurrentTransferChecks']


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def check(path, expected):
    require(sha(path) == expected, 'Changed pin: ' + str(path))


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def imports(path):
    s = Path(path).read_text()
    out, i, depth, string = [], 0, 0, False
    while i < len(s):
        if depth:
            if s.startswith('/-', i):
                depth += 1
                i += 2
            elif s.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                out.append('\n' if s[i] == '\n' else ' ')
                i += 1
        elif string:
            if s[i] == '\\':
                i += 2
            elif s[i] == '"':
                string = False
                i += 1
            else:
                out.append('\n' if s[i] == '\n' else ' ')
                i += 1
        elif s.startswith('/-', i):
            depth = 1
            i += 2
        elif s.startswith('--', i):
            j = s.find('\n', i)
            i = len(s) if j < 0 else j
        elif s[i] == '"':
            string = True
            i += 1
        else:
            out.append(s[i])
            i += 1
    return re.findall(r'^\s*(?:(?:public|private)\s+)?import\s+([\w.]+)',
                      ''.join(out), re.M)


def objects(record):
    if 'objects' in record:
        return record['objects']
    return [{'path': record['object'], 'sha256': record['object_sha256']}]


def verify(d):
    for p in d['pins']:
        check(p['path'], p['sha256'])
    for name, p in d['package_identity'].items():
        check(ROOT / name, p['current_sha256'])
    check(d['compiler']['path'], d['compiler']['sha256'])
    require(shutil.disk_usage(ROOT).free >= 512 * 1024**2, '512 MiB disk reserve')


def prepare():
    require(not MANIFEST.exists(), 'Preparation already exists')
    parents = [REV / 'current-equation-narrow-dependency-replay.json',
               REV / 'foundation-ha-peano-dependency-replay.json']
    docs = [json.loads(p.read_text()) for p in parents]
    selected, pins, alternatives = {}, [], []
    for parent, d in zip(parents, docs):
        pins.append({'path': str(parent), 'sha256': sha(parent)})
        records = d['modules'] + [r for r in d['fresh_modules']
                                 if not r['module'].endswith('Checks')]
        for r in records:
            pins.append({'path': r['source'], 'sha256': r['source_sha256']})
            pins.extend({'path': o['path'], 'sha256': o['sha256']} for o in objects(r))
            if 'trace' in r:
                pins.append({'path': r['trace'], 'sha256': r['trace_sha256']})
            if r['module'] in selected:
                old = selected[r['module']]
                require(old['source_sha256'] == r['source_sha256'], 'Source conflict')
                if objects(old) != objects(r):
                    alternatives.append({'module': r['module'], 'record': r,
                                         'provenance': str(parent)})
            else:
                selected[r['module']] = dict(r, reused_from=str(parent))
    private = Path(tempfile.mkdtemp(prefix='foundation-ha-current-transfer-'))
    lib = private / 'lib'
    paths = docs[0]['lean_path'].split(':')[1:]
    external = {}
    for r in selected.values():
        r['imports'] = imports(r['source'])
        for name in r['imports']:
            if name in selected:
                continue
            found = next((Path(p) / (name.replace('.', '/') + '.olean') for p in paths
                          if (Path(p) / (name.replace('.', '/') + '.olean')).is_file()), None)
            require(found is not None, 'Missing import: ' + name)
            external[name] = {'module': name, 'path': str(found), 'sha256': sha(found),
                              'scope': 'Existing package/toolchain object boundary; not fresh'}
    pins.extend({'path': r['path'], 'sha256': r['sha256']} for r in external.values())
    d = {'scope': 'Two new fresh leaves; exact-source private reuse, no Foundation/native rebuild',
         'snapshot': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
         'private': str(private), 'modules': list(selected.values()), 'pins': pins,
         'authenticated_alternatives': alternatives, 'external': list(external.values()),
         'compiler': docs[0]['compiler'], 'package_identity': docs[0]['package_identity'],
         'lean_path': ':'.join([str(lib)] + paths), 'parents': [str(p) for p in parents]}
    require(docs[0]['compiler'] == docs[1]['compiler'], 'Compiler mismatch')
    require(docs[0]['package_identity'] == docs[1]['package_identity'], 'Package mismatch')
    verify(d)
    for r in selected.values():
        for o in objects(r):
            op = Path(o['path'])
            suffix = op.name[len(r['module'].split('.')[-1]):]
            dest = lib / (r['module'].replace('.', '/') + suffix)
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.symlink_to(op)
    dump(MANIFEST, d)
    print(json.dumps({'private': str(private), 'modules': len(selected),
                      'foundation': sum(n.startswith('Foundation.') for n in selected),
                      'external': len(external), 'pins': len(pins)}))


def run(name):
    require(name in LEAVES, 'Unexpected leaf')
    d = json.loads(MANIFEST.read_text())
    verify(d)
    private = Path(d['private'])
    stamp = str(time.time_ns())
    source = SRC / (name + '.lean')
    snapshot = BUNDLE / (stamp + '-' + name + '.lean')
    shutil.copyfile(source, snapshot)
    log = BUNDLE / (stamp + '-' + name + '.log')
    target = private / 'lib/DiophantineConsistency' / (name + '.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    cmd = [d['compiler']['path'], '-M6000', '-j1', '-DElab.async=false', '-o', str(target), str(source)]
    env = dict(os.environ, LEAN_PATH=d['lean_path'])
    start = time.monotonic()
    with log.open('w') as f:
        p = subprocess.run(cmd, cwd=ROOT, env=env, stdout=f, stderr=subprocess.STDOUT)
    r = {'module': 'DiophantineConsistency.' + name, 'source': str(source),
         'source_sha256': sha(snapshot), 'snapshot': str(snapshot), 'command': cmd,
         'exit_code': p.returncode, 'seconds': time.monotonic() - start,
         'log': str(log), 'log_sha256': sha(log), 'driver_sha256': sha(__file__)}
    if p.returncode == 0:
        r.update(object=str(target), object_sha256=sha(target))
    dump(BUNDLE / (stamp + '-' + name + '.json'), r)
    verify(d)
    check(source, r['source_sha256'])
    print(json.dumps(r))
    print(log.read_text())
    sys.exit(p.returncode)


if __name__ == '__main__':
    if sys.argv[1:] == ['prepare']:
        prepare()
    elif len(sys.argv) == 3 and sys.argv[1] == 'run':
        run(sys.argv[2])
    else:
        raise RuntimeError('Use prepare or run LEAF')
