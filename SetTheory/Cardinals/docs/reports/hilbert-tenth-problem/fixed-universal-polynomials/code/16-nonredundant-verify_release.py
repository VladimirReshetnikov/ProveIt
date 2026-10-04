#!/usr/bin/env python3
"""Strict, identity-gated Report39 replay in fresh external copies.

This authenticates a release and reproduces finite checks, not an unbounded
sign theorem. Authenticate the complete archive with a trusted external hash
tool before executing this program; its own PASS is not an authenticity anchor.
"""
import argparse
import ast
import hashlib
import json
import math
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import subprocess
import sys
import tempfile

MANIFEST_SHA256 = "e19f92e5d2a3dc714b4b9d0a2b1e9042d068ed0e1e3744d699aa981f5db3efa2"
ROOT = Path(__file__).resolve().parent
PIN_PATTERN = rb'(?m)^MANIFEST_SHA256 = "[0-9a-f]{64}"$'
ZERO_PIN_LINE = b'MANIFEST_SHA256 = "' + b'0'*64 + b'"'
HASH_CONVENTION = 'sha256; verify_release.py self-pin line normalized to 64 zeros; all other files byte-exact'
SOURCE_SUMS_PIN = 'b769c58935f5951b1ad4b23df0daa5a9c31e2a04ea734d7bb9916249e51e9c38'
JACOBI_SUMS_PIN = '27203cb0baa757bbbf05d166c379dd9da8ceeeed084ec131cc9558749dae5cf4'
JACOBI_PROOF_PIN = '16311c258666483ed3342e3129966018e33a17ff0ec71aceca50540b1a75c98a'
PROOF_PIN = 'd67a98bd95a1a11a8b1dc24c508c601f92c6758f9c4d92d9d4d13acb85936575'
MATH_SCRIPTS = {'evidence/check_unwrapped_family.py': '2ddc7a8ccc2ce7b1352030d7b9905957df1838ed8fa5628cbab39b2b0fcf091d', 'evidence/independent/check_audit.py': '8e2f6f8fc97f0d57f9ac8d29a2c00075c3d8d9b82613f2217e5db54df507d4ae', 'jacobi/check_jacobi_addendum.py': '6e33f7d2452d510bed14c8097428b746c86b3b06719e4e2d5c987920feb05482'}
CHECKS = [{'label': 'authored-exact-checks', 'script': 'evidence/check_unwrapped_family.py', 'expected': 'evidence/expected_check_results.json', 'receipt': 'evidence/expected_check_results.json', 'capture': 'stdout'}, {'label': 'independent-symbolic-audit', 'script': 'evidence/independent/check_audit.py', 'expected': 'evidence/independent/expected_audit_receipt.json', 'receipt': 'evidence/independent/audit_receipt.json', 'capture': 'stdout'}, {'label': 'jacobi-addendum-exact-checks', 'script': 'jacobi/check_jacobi_addendum.py', 'expected': 'jacobi/expected_jacobi_receipt.json', 'receipt': 'jacobi/expected_jacobi_receipt.json', 'capture': 'stdout', 'staging': 'authenticated-external-portable-layout'}]


def need(condition, message):
    if condition is not True:
        raise RuntimeError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def normalized_verifier(raw):
    need(len(re.findall(PIN_PATTERN, raw)) == 1, 'Identity gate: verifier pin format')
    return re.sub(PIN_PATTERN, ZERO_PIN_LINE, raw)


def parse_json(raw, label='JSON'):
    def unique(pairs):
        out = {}
        for key, value in pairs:
            need(key not in out, label + ': duplicate key: ' + key)
            out[key] = value
        return out
    def reject(value):
        raise RuntimeError(label + ': nonfinite number: ' + value)
    def finite(value):
        result = float(value)
        need(math.isfinite(result), label + ': nonfinite numeric overflow')
        return result
    try:
        return json.loads(raw, object_pairs_hook=unique, parse_constant=reject, parse_float=finite)
    except (ValueError, UnicodeDecodeError) as exc:
        raise RuntimeError(label + ': malformed JSON') from exc


def read_json(path):
    return parse_json(path.read_bytes(), path.name)


def typed_equal(actual, expected, label='receipt'):
    need(type(actual) is type(expected), label + ': exact JSON type mismatch')
    if type(expected) is dict:
        need(set(actual) == set(expected), label + ': exact key set mismatch')
        for key in expected:
            typed_equal(actual[key], expected[key], label + '.' + key)
    elif type(expected) is list:
        need(len(actual) == len(expected), label + ': exact list length mismatch')
        for i, (a, b) in enumerate(zip(actual, expected)):
            typed_equal(a, b, label + '[' + str(i) + ']')
    else:
        need(actual == expected, label + ': exact value mismatch')


def safe_relative(name):
    need(type(name) is str and re.fullmatch(r'[A-Za-z0-9_./-]+', name) is not None, 'Identity gate: unsafe path')
    p = PurePosixPath(name)
    need(not p.is_absolute() and all(v not in ('', '.', '..') for v in name.split('/')), 'Identity gate: unsafe component')
    need(p.as_posix() == name, 'Identity gate: noncanonical path')
    return p


def snapshot(root):
    need(root.is_dir() and not root.is_symlink(), 'Identity gate: invalid root')
    out = {}
    for p in [root] + sorted(root.rglob('*')):
        name = p.relative_to(root).as_posix()
        s = p.lstat()
        need(not p.is_symlink(), 'Identity gate: symlink: ' + name)
        need(stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode), 'Identity gate: special file: ' + name)
        out[name] = (sha(p.read_bytes()) if p.is_file() else None, stat.S_IMODE(s.st_mode), s.st_mtime_ns)
    return out


def verify_approval(root):
    p = root/'verification/release-review.json'
    need(p.is_file(), 'Identity gate: final release approval record missing')
    review = read_json(p)
    need(type(review) is dict and {'schema','status','source_sums_sha256','proof_sha256'} <= set(review), 'Identity gate: release review shape')
    need(review['schema'] == 'report39-release-review-v1' and review['status'] == 'APPROVED', 'Identity gate: release review is not approved')
    need(review['source_sums_sha256'] == SOURCE_SUMS_PIN and review['proof_sha256'] == PROOF_PIN, 'Identity gate: release approval source identity mismatch')
    need(review.get('jacobi_sums_sha256') == JACOBI_SUMS_PIN and review.get('jacobi_proof_sha256') == JACOBI_PROOF_PIN, 'Identity gate: release approval Jacobi identity mismatch')
    for suffix in ('tex','pdf'):
        need(review.get('article_'+suffix+'_sha256') == sha((root/('Research_Report39.'+suffix)).read_bytes()), 'Identity gate: final article approval identity mismatch: '+suffix)


def verify_identity(root=ROOT):
    need(MANIFEST_SHA256 != '0'*64, 'Identity gate: release is not sealed')
    before = snapshot(root)
    raw = (root/'MANIFEST.json').read_bytes()
    need(sha(raw) == MANIFEST_SHA256, 'Identity gate: enclosing manifest digest mismatch')
    doc = parse_json(raw, 'Identity gate: manifest')
    need(type(doc) is dict and set(doc) == {'schema', 'release_stage', 'files', 'file_count', 'hash_convention'}, 'Identity gate: manifest shape')
    need(doc['schema'] == 'report39-release-inventory-v1', 'Identity gate: manifest schema')
    need(doc['release_stage'] in ('engineering-preview', 'final'), 'Identity gate: release stage')
    need(doc['hash_convention'] == HASH_CONVENTION, 'Identity gate: hash convention')
    files = doc['files']
    need(type(files) is dict and type(doc['file_count']) is int and doc['file_count'] == len(files), 'Identity gate: file count type/value')
    need('verify_release.py' in files, 'Identity gate: missing verifier')
    dirs = {'.'}
    for name, record in files.items():
        rel = safe_relative(name)
        need(name not in ('MANIFEST.json', 'SHA256SUMS'), 'Identity gate: recursive inventory entry')
        need(type(record) is dict and set(record) == {'bytes', 'sha256', 'mode'}, 'Identity gate: entry shape')
        need(type(record['bytes']) is int and record['bytes'] >= 0, 'Identity gate: byte size type/value')
        need(type(record['mode']) is int and record['mode'] in (0o644, 0o755), 'Identity gate: file mode type/value')
        need(type(record['sha256']) is str and re.fullmatch('[0-9a-f]{64}', record['sha256']) is not None, 'Identity gate: digest type/value')
        dirs.update(p.as_posix() for p in rel.parents)
    actual_files = {n for n, v in before.items() if v[0] is not None}
    actual_dirs = set(before) - actual_files
    need(actual_files == set(files) | {'MANIFEST.json', 'SHA256SUMS'} and actual_dirs == dirs, 'Identity gate: exact path inventory mismatch')
    for name, record in files.items():
        raw = (root/name).read_bytes()
        canonical = normalized_verifier(raw) if name == 'verify_release.py' else raw
        need(len(raw) == record['bytes'] and sha(canonical) == record['sha256'], 'Identity gate: payload digest mismatch: ' + name)
        need(before[name][1] == record['mode'], 'Identity gate: payload mode mismatch: ' + name)
    need(all(before[n][1] == 0o755 for n in actual_dirs), 'Identity gate: directory mode mismatch')
    need(before['MANIFEST.json'][1] == 0o644 and before['SHA256SUMS'][1] == 0o644, 'Identity gate: inventory mode mismatch')
    sums = ''.join(sha((root/n).read_bytes()) + '  ' + n + '\n' for n in sorted(set(files) | {'MANIFEST.json'}))
    need((root/'SHA256SUMS').read_bytes() == sums.encode('utf-8'), 'Identity gate: checksum inventory mismatch')
    if doc['release_stage'] == 'final':
        need({'Research_Report39.tex', 'Research_Report39.pdf'} <= set(files), 'Identity gate: final article missing')
        verify_approval(root)
    for name in files:
        p = root/name
        # Upstream source programs are preserved as inert bytes, not parsed or run.
        if p.suffix == '.py' and (not name.startswith('evidence/') or name in MATH_SCRIPTS):
            need(not any(isinstance(n, ast.Assert) for n in ast.walk(ast.parse(p.read_bytes()))), 'Identity gate: optimization-disabled assertion: ' + name)
        if p.suffix == '.json':
            read_json(p)
        if not name.startswith('evidence/') and p.suffix in ('.py', '.json', '.md', '.tex', '.sh', '.txt'):
            raw = p.read_bytes()
            for prefix in (b'/' + b'workspace/', b'/' + b'home/', b'/' + b'root/'):
                need(prefix not in raw, 'Identity gate: private absolute path: ' + name)
    source = root/'evidence'
    raw_sums = (source/'MANIFEST.sha256').read_bytes()
    need(sha(raw_sums) == SOURCE_SUMS_PIN, 'Identity gate: frozen source manifest pin mismatch')
    rows = raw_sums.decode('ascii').splitlines()
    need(len(rows) == 21, 'Identity gate: frozen source payload count')
    source_names = set()
    for row in rows:
        match = re.fullmatch(r'([0-9a-f]{64})  ([A-Za-z0-9_./-]+)', row)
        need(match is not None, 'Identity gate: frozen source checksum format')
        digest,name = match.groups();safe_relative(name)
        need(name not in source_names and name != 'MANIFEST.sha256', 'Identity gate: duplicate/recursive source entry')
        source_names.add(name)
        need(sha((source/name).read_bytes()) == digest, 'Identity gate: frozen source bytes changed: '+name)
    source_names.add('MANIFEST.sha256')
    need({name for name in files if name.startswith('evidence/')} == {'evidence/'+n for n in source_names}, 'Identity gate: source inventory is not the exact frozen 22-file packet')
    need(sha((source/'ALL-BUT-MAIN-PROJECTION.md').read_bytes()) == PROOF_PIN, 'Identity gate: proof pin mismatch')
    for name,digest in MATH_SCRIPTS.items():
        need(sha((root/name).read_bytes()) == digest, 'Identity gate: mathematical executable pin mismatch')
    lineage = read_json(root/'verification/source-lineage.json')
    expected_lineage = {'schema':'report39-source-lineage-v1','inventory_authority':'frozen source MANIFEST.sha256; 21 payload files plus the checksum manifest','files':[]}
    for name in sorted(source_names):
        digest = sha((source/name).read_bytes())
        expected_lineage['files'].append({'packet':'unwrapped-odd-index-followon-20261003','original_relative_path':name,'packaged_relative_path':'evidence/'+name,'original_sha256':digest,'packaged_sha256':digest,'normalization':'none; byte-exact','role':'inert upstream source context' if name.startswith('context/') else 'complete frozen unwrapped-family packet member'})
    typed_equal(lineage, expected_lineage, 'Identity gate: exact source lineage')
    jacobi = root/'jacobi'
    jacobi_sums = (jacobi/'MANIFEST.sha256').read_bytes()
    need(sha(jacobi_sums) == JACOBI_SUMS_PIN, 'Identity gate: Jacobi source manifest pin mismatch')
    jacobi_rows = jacobi_sums.decode('ascii').splitlines()
    need(len(jacobi_rows) == 31, 'Identity gate: Jacobi payload count')
    jacobi_names = set()
    jacobi_lineage = {'schema':'report39-jacobi-lineage-v1','inventory_authority':'frozen Jacobi MANIFEST.sha256; 31 payload files plus the checksum manifest','deduplication':'22 inherited-family members map byte-exactly to evidence/; portable layout assembled only in external replay copies','files':[]}
    for row in jacobi_rows:
        match = re.fullmatch(r'([0-9a-f]{64})  ([A-Za-z0-9_./-]+)', row)
        need(match is not None, 'Identity gate: Jacobi checksum format')
        digest,name = match.groups();safe_relative(name)
        need(name not in jacobi_names and name != 'MANIFEST.sha256', 'Identity gate: duplicate/recursive Jacobi source entry')
        jacobi_names.add(name)
        packaged = 'evidence/'+name[len('inherited-family/'):] if name.startswith('inherited-family/') else 'jacobi/'+name
        need(sha((root/packaged).read_bytes()) == digest, 'Identity gate: frozen Jacobi bytes changed: '+name)
    need({n[len('inherited-family/'):] for n in jacobi_names if n.startswith('inherited-family/')} == source_names, 'Identity gate: deduplicated inherited family inventory mismatch')
    jacobi_names.add('MANIFEST.sha256')
    need({name for name in files if name.startswith('jacobi/')} == {'jacobi/'+n for n in jacobi_names if not n.startswith('inherited-family/')}, 'Identity gate: exact Jacobi inventory mismatch')
    need(sha((jacobi/'JACOBI-ADDENDUM.md').read_bytes()) == JACOBI_PROOF_PIN, 'Identity gate: Jacobi proof pin mismatch')
    for name in sorted(jacobi_names):
        inherited = name.startswith('inherited-family/')
        packaged = 'evidence/'+name[len('inherited-family/'):] if inherited else 'jacobi/'+name
        digest = sha((root/packaged).read_bytes())
        jacobi_lineage['files'].append({'packet':'jacobi-unwrapped-addendum-20261003','original_relative_path':name,'packaged_relative_path':packaged,'original_sha256':digest,'packaged_sha256':digest,'normalization':'none; byte-exact','role':'deduplicated inherited family packet member' if inherited else 'frozen Jacobi addendum member'})
    typed_equal(read_json(root/'verification/jacobi-lineage.json'), jacobi_lineage, 'Identity gate: exact Jacobi lineage')
    expected = read_json(root/'verification/expected-receipts.json')
    need(type(expected) is dict and set(expected) == {c['receipt'] for c in CHECKS}, 'Identity gate: expected receipt inventory')
    for check in CHECKS:
        typed_equal(read_json(root/check['receipt']), expected[check['receipt']], 'Identity gate: stored '+check['receipt'])
        typed_equal(read_json(root/check['expected']), expected[check['receipt']], 'Identity gate: expected '+check['expected'])
        need((root/check['receipt']).read_bytes() == (root/check['expected']).read_bytes(), 'Identity gate: stored/expected receipt bytes differ')
    typed_equal(read_json(root/'verification/replay-plan.json'), {'schema':'report39-replay-plan-v1','runtime':'Python 3.9+; SymPy 1.14.0 for the independent checker','checks':CHECKS}, 'Identity gate: exact replay plan')
    return doc, before


def semantic_regression():
    cases = [(True,1),(False,0),(1,True),(1.0,1),({'n':True},{'n':1}),({'sos':False},{'sos':0}),([False],[0]),({'n':1,'extra':0},{'n':1}),({},{'n':1}),([1],[1,2]),(None,0),('1',1),({'a':[{'n':True}]},{'a':[{'n':1}]}),({'x':[1.0]},{'x':[1]}),({'x':[1]},{'x':[1.0]}),('false',False),(None,False),([1],{'0':1})]
    for a,b in cases:
        try:typed_equal(a,b)
        except RuntimeError:pass
        else:raise RuntimeError('Strict comparator accepted a mutation')
    malformed = ['{"x":1,"x":1}', '{"n":NaN}', '{"n":Infinity}', '{"n":-Infinity}', '{"n":1e9999}', '{', '[1,]', '{"n":01}', b'\xff', '{"nested":{"x":1,"x":1}}', '{"x":[NaN]}', '{"x":-1e9999}']
    for raw in malformed:
        try:parse_json(raw)
        except RuntimeError:pass
        else:raise RuntimeError('Strict parser accepted malformed JSON')
    valid = {'ok':True,'count':1,'zero':0,'x':[None,'a',1.5]}
    typed_equal(parse_json(json.dumps(valid)),valid)
    return {'status':'PASS','typed_mutations_rejected':len(cases),'malformed_json_rejected':len(malformed)}


def external_temp_parent():
    # Do not call tempfile.gettempdir(): its writable-directory probe can touch
    # the release itself when TMPDIR or the current directory is unsafe.
    candidates = [os.environ[k] for k in ('TMPDIR','TEMP','TMP') if os.environ.get(k)]
    candidates += ['/tmp','/var/tmp']
    for value in candidates:
        candidate = Path(value).resolve()
        need(candidate != ROOT and ROOT not in candidate.parents, 'Temporary parent must be outside the release')
        if candidate.is_dir() and os.access(candidate, os.W_OK | os.X_OK):
            return candidate
    raise RuntimeError('No writable external temporary parent is available')


def runtime_identity():
    need(sys.version_info >= (3,9), 'Replay requires Python 3.9+')
    result = subprocess.run([sys.executable,'-I','-B','-c',
        "import importlib.metadata; print(importlib.metadata.version('sympy'))"],
        capture_output=True,text=True,timeout=60)
    need(result.returncode == 0 and not result.stderr.strip(), 'SymPy distribution metadata unavailable')
    need(result.stdout == '1.14.0\n', 'Replay requires exactly SymPy 1.14.0; no dependency is installed automatically')
    return {'python_minimum':'3.9','sympy':'1.14.0','automatic_installation':False}


def receipt_directory(value):
    if value is None:
        return None
    path = Path(value).resolve()
    need(path != ROOT and ROOT not in path.parents, 'Receipt directory must be external')
    need(not path.exists(), 'Receipt directory must be new; existing paths are never overwritten')
    need(path.parent.is_dir(), 'Receipt directory parent must already exist')
    return path


def stage_jacobi(work,temporary_parent):
    # Rebuild the frozen portable layout outside both release copies, without
    # changing any frozen program or placing duplicate inherited files in ZIPs.
    stage = temporary_parent/'jacobi-portable-layout'
    shutil.copytree(work/'jacobi',stage,copy_function=shutil.copy2)
    shutil.copytree(work/'evidence',stage/'inherited-family',copy_function=shutil.copy2)
    before = snapshot(stage)
    expected = {}
    for prefix,source in [('',work/'jacobi'),('inherited-family/',work/'evidence')]:
        for p in sorted(source.rglob('*')):
            if p.is_file():
                expected[prefix+p.relative_to(source).as_posix()] = (sha(p.read_bytes()),stat.S_IMODE(p.stat().st_mode))
    actual = {name:(record[0],record[1]) for name,record in before.items() if record[0] is not None}
    typed_equal(actual,expected,'Identity gate: staged Jacobi exact bytes/modes')
    directories = {'.'}
    for name in expected:
        directories.update(p.as_posix() for p in PurePosixPath(name).parents)
    need({n for n,v in before.items() if v[0] is None} == directories, 'Identity gate: staged Jacobi exact directories')
    need(all(v[1] == 0o755 for v in before.values() if v[0] is None), 'Identity gate: staged Jacobi directory modes')
    return stage,before


def full_replay(work_parent=None,receipt_output=None):
    manifest,before = verify_identity()
    expected = read_json(ROOT/'verification/expected-receipts.json')
    destination = receipt_directory(receipt_output)
    runtime = runtime_identity()
    if work_parent is not None:
        work_parent = Path(work_parent).resolve()
        need(work_parent != ROOT and ROOT not in work_parent.parents, 'Replay directory must be external')
        work_parent.mkdir(parents=True,exist_ok=True)
    else:
        work_parent = external_temp_parent()
    env = {k:v for k,v in os.environ.items() if not k.startswith('PYTHON')}
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    modes = {}
    exports = {}
    for mode,optimized in [('normal',False),('optimized',True)]:
        with tempfile.TemporaryDirectory(prefix='report39-'+mode+'-', dir=work_parent) as tmp:
            work = Path(tmp)/'relocated-release'
            shutil.copytree(ROOT,work,copy_function=shutil.copy2)
            _,copied_before = verify_identity(work)
            records = {}
            for check in CHECKS:
                # Authenticated authored scripts print fresh receipts; no source
                # receipt is opened for writing, and no upstream program executes.
                need(check['script'] in MATH_SCRIPTS, 'Replay executable is not allowlisted')
                program = work/check['script']
                staged = staged_before = None
                if check.get('staging') == 'authenticated-external-portable-layout':
                    staged,staged_before = stage_jacobi(work,Path(tmp))
                    program = staged/'check_jacobi_addendum.py'
                    need(sha(program.read_bytes()) == MATH_SCRIPTS[check['script']], 'Identity gate: staged Jacobi executable pin')
                cmd = [sys.executable,'-I','-B'] + (['-O'] if optimized else []) + [str(program),'--expect',str(work/check['expected'])]
                result = subprocess.run(cmd,cwd=Path(tmp),env=env,capture_output=True,timeout=1800)
                need(result.returncode == 0,'Replay failed: ' + check['label'] + ': ' + result.stderr[-3000:].decode('utf-8','replace'))
                need(not result.stderr.strip(),'Unexpected replay stderr: ' + check['label'])
                receipt = parse_json(result.stdout, check['label']+' '+mode)
                typed_equal(receipt,expected[check['receipt']],check['label']+' '+mode)
                need(result.stdout == (ROOT/check['receipt']).read_bytes(),'Replay receipt byte inequality: '+check['label'])
                exports[mode+'-'+check['label']+'.json'] = result.stdout
                records[check['label']] = {'status':'PASS','receipt_sha256':sha(result.stdout),'stdout_bytes':len(result.stdout)}
                if staged is not None:
                    need(snapshot(staged) == staged_before,'Staged Jacobi bytes/modes/mtimes changed')
                need(snapshot(work) == copied_before,'Copied release bytes/modes/mtimes changed: '+check['label'])
                verify_identity(work)
            modes[mode] = records
    typed_equal(modes['normal'],modes['optimized'],'normal/optimized replay')
    regression = semantic_regression()
    need(snapshot(ROOT) == before,'Original release bytes/modes/mtimes changed during replay')
    verify_identity()
    if destination is not None:
        destination.mkdir()
        for name,raw in exports.items():
            with (destination/name).open('xb') as stream:
                stream.write(raw)
    return {'schema':'report39-replay-v1','runtime':runtime,'external_receipts_exported':destination is not None,'jacobi_portable_staging_authenticated':True,'status':'PASS','manifest_sha256':MANIFEST_SHA256,'release_stage':manifest['release_stage'],'identity_verified_before_copied_execution':True,'fresh_external_copies':2,'normal_optimized_receipt_bytes_equal':True,'original_and_copied_bytes_modes_mtimes_preserved':True,'upstream_sources_executed':False,'mathematical_executables':sorted(MATH_SCRIPTS),'strict_receipt_regression':regression,'modes':modes,'scope':'Finite subsystem corroboration; infinite reduced-predicate theorem is conditional on inherited premises and proved analytically, not by sampling. Jacobi addendum proves infinitely many genuine reduced-system misses and comparison nonredundancy. No main-congruence hit, full negative zero or global sign theorem is established; the symbol -1 sector remains unresolved.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--verify-only',action='store_true')
    group.add_argument('--self-test-types',action='store_true')
    group.add_argument('--replay',action='store_true')
    parser.add_argument('--workdir',help='external parent for disposable replay copies')
    parser.add_argument('--receipt-dir',help='new external directory for six fresh stdout receipts; parent must exist')
    args = parser.parse_args()
    need(args.replay or (args.workdir is None and args.receipt_dir is None), '--workdir and --receipt-dir require --replay')
    if args.self_test_types:
        result = semantic_regression()
    elif args.verify_only:
        doc,_ = verify_identity()
        result = {'schema':'report39-identity-v1','status':'PASS','manifest_sha256':MANIFEST_SHA256,'release_stage':doc['release_stage'],'file_count':doc['file_count']}
    else:
        result = full_replay(args.workdir,args.receipt_dir)
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__ == '__main__':
    try:main()
    except (RuntimeError,OSError,ValueError,SyntaxError,RecursionError,subprocess.SubprocessError) as exc:
        print(str(exc),file=sys.stderr)
        raise SystemExit(1)
