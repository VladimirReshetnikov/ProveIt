#!/usr/bin/env python3
"""Strict, identity-gated Report37 replay in fresh external copies.

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

MANIFEST_SHA256 = "0e349f619b91ad2be3a915bbc6804c255d83d750da393b72f93205f4b1ea0bd6"
ROOT = Path(__file__).resolve().parent
PIN_PATTERN = rb'(?m)^MANIFEST_SHA256 = "[0-9a-f]{64}"$'
ZERO_PIN_LINE = b'MANIFEST_SHA256 = "' + b'0'*64 + b'"'
HASH_CONVENTION = 'sha256; verify_release.py self-pin line normalized to 64 zeros; all other files byte-exact'
SOURCE_SUMS_PIN = '793b955c11fa905df10e69e93e0c02a3c64af8a6566c71b059fad8363e450e0c'
PROOF_PIN = '918b82b7666b4f5cbab5fd7a0b8298275ac62fe84f83261ef88ea863765d455f'
MATH_SCRIPTS = {
    'evidence/check_exact_obstruction.py': 'a96a298338a5714018fda4d23e9f4a4c4f82eb34f0550b71ca06e2f0e2826189',
    'evidence/independent/audit_exact_obstruction.py': 'fb186f9ebeeceebbd85b2c4373c61ab0606bb69603250440ec2a27253cb28816',
    'evidence/independent/audit_log_windows.py': '2fe82add15b10f4b49e7899e84a1e018aa34b8c209a63b206547230eadd2d812',
}
CHECKS = [
    {'label':'authored-exact-checks','script':'evidence/check_exact_obstruction.py','expected':'evidence/expected_check_results.json','receipt':'evidence/check_results.json','capture':'stdout'},
    {'label':'independent-exact-audit','script':'evidence/independent/audit_exact_obstruction.py','expected':'evidence/independent/expected_audit_results.json','receipt':'evidence/independent/audit_results.json','capture':'stdout'},
    {'label':'independent-log-windows','script':'evidence/independent/audit_log_windows.py','expected':'evidence/independent/expected_log_window_results.json','receipt':'evidence/independent/log_window_results.json','capture':'stdout'},
]


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
    need(review['schema'] == 'report37-release-review-v1' and review['status'] == 'APPROVED', 'Identity gate: release review is not approved')
    need(review['source_sums_sha256'] == SOURCE_SUMS_PIN and review['proof_sha256'] == PROOF_PIN, 'Identity gate: release approval source identity mismatch')
    for suffix in ('tex','pdf'):
        need(review.get('article_'+suffix+'_sha256') == sha((root/('Research_Report37.'+suffix)).read_bytes()), 'Identity gate: final article approval identity mismatch: '+suffix)


def verify_identity(root=ROOT):
    need(MANIFEST_SHA256 != '0'*64, 'Identity gate: release is not sealed')
    before = snapshot(root)
    raw = (root/'MANIFEST.json').read_bytes()
    need(sha(raw) == MANIFEST_SHA256, 'Identity gate: enclosing manifest digest mismatch')
    doc = parse_json(raw, 'Identity gate: manifest')
    need(type(doc) is dict and set(doc) == {'schema', 'release_stage', 'files', 'file_count', 'hash_convention'}, 'Identity gate: manifest shape')
    need(doc['schema'] == 'report37-release-inventory-v1', 'Identity gate: manifest schema')
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
    need((root/'SHA256SUMS').read_text(encoding='utf-8') == sums, 'Identity gate: checksum inventory mismatch')
    if doc['release_stage'] == 'final':
        need({'Research_Report37.tex', 'Research_Report37.pdf'} <= set(files), 'Identity gate: final article missing')
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
    need(len(rows) == 25, 'Identity gate: frozen source payload count')
    source_names = set()
    for row in rows:
        match = re.fullmatch(r'([0-9a-f]{64})  ([A-Za-z0-9_./-]+)', row)
        need(match is not None, 'Identity gate: frozen source checksum format')
        digest,name = match.groups();safe_relative(name)
        need(name not in source_names and name != 'MANIFEST.sha256', 'Identity gate: duplicate/recursive source entry')
        source_names.add(name)
        need(sha((source/name).read_bytes()) == digest, 'Identity gate: frozen source bytes changed: '+name)
    source_names.add('MANIFEST.sha256')
    need({name for name in files if name.startswith('evidence/')} == {'evidence/'+n for n in source_names}, 'Identity gate: source inventory is not the exact frozen 26-file packet')
    need(sha((source/'EXACT-OBSTRUCTION.md').read_bytes()) == PROOF_PIN, 'Identity gate: proof pin mismatch')
    for name,digest in MATH_SCRIPTS.items():
        need(sha((root/name).read_bytes()) == digest, 'Identity gate: mathematical executable pin mismatch')
    lineage = read_json(root/'verification/source-lineage.json')
    expected_lineage = {'schema':'report37-source-lineage-v1','inventory_authority':'frozen source MANIFEST.sha256; 25 payload files plus the checksum manifest','files':[]}
    for name in sorted(source_names):
        digest = sha((source/name).read_bytes())
        expected_lineage['files'].append({'packet':'positive-index-restoration-followon-20261003','original_relative_path':name,'packaged_relative_path':'evidence/'+name,'original_sha256':digest,'packaged_sha256':digest,'normalization':'none; byte-exact','role':'inert upstream source context' if name.startswith('sources/') else 'complete frozen obstruction packet member'})
    typed_equal(lineage, expected_lineage, 'Identity gate: exact source lineage')
    expected = read_json(root/'verification/expected-receipts.json')
    need(type(expected) is dict and set(expected) == {c['receipt'] for c in CHECKS}, 'Identity gate: expected receipt inventory')
    for check in CHECKS:
        typed_equal(read_json(root/check['receipt']), expected[check['receipt']], 'Identity gate: stored '+check['receipt'])
        typed_equal(read_json(root/check['expected']), expected[check['receipt']], 'Identity gate: expected '+check['expected'])
        need((root/check['receipt']).read_bytes() == (root/check['expected']).read_bytes(), 'Identity gate: stored/expected receipt bytes differ')
    typed_equal(read_json(root/'verification/replay-plan.json'), {'schema':'report37-replay-plan-v1','runtime':'Python 3.9+ standard library only','checks':CHECKS}, 'Identity gate: exact replay plan')
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


def full_replay(work_parent=None):
    manifest,before = verify_identity()
    expected = read_json(ROOT/'verification/expected-receipts.json')
    if work_parent is not None:
        work_parent = Path(work_parent).resolve()
        need(work_parent != ROOT and ROOT not in work_parent.parents, 'Replay directory must be external')
        work_parent.mkdir(parents=True,exist_ok=True)
    else:
        work_parent = external_temp_parent()
    env = {k:v for k,v in os.environ.items() if not k.startswith('PYTHON')}
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    modes = {}
    for mode,optimized in [('normal',False),('optimized',True)]:
        with tempfile.TemporaryDirectory(prefix='report37-'+mode+'-', dir=work_parent) as tmp:
            work = Path(tmp)/'relocated-release'
            shutil.copytree(ROOT,work,copy_function=shutil.copy2)
            _,copied_before = verify_identity(work)
            records = {}
            for check in CHECKS:
                # Authenticated authored scripts print fresh receipts; no source
                # receipt is opened for writing, and no upstream program executes.
                need(check['script'] in MATH_SCRIPTS, 'Replay executable is not allowlisted')
                cmd = [sys.executable,'-I','-B'] + (['-O'] if optimized else []) + [str(work/check['script']),'--expect',str(work/check['expected'])]
                result = subprocess.run(cmd,cwd=Path(tmp),env=env,capture_output=True,timeout=1800)
                need(result.returncode == 0,'Replay failed: ' + check['label'] + ': ' + result.stderr[-3000:].decode('utf-8','replace'))
                need(not result.stderr.strip(),'Unexpected replay stderr: ' + check['label'])
                receipt = parse_json(result.stdout, check['label']+' '+mode)
                typed_equal(receipt,expected[check['receipt']],check['label']+' '+mode)
                need(result.stdout == (ROOT/check['receipt']).read_bytes(),'Replay receipt byte inequality: '+check['label'])
                records[check['label']] = {'status':'PASS','receipt_sha256':sha(result.stdout),'stdout_bytes':len(result.stdout)}
                need(snapshot(work) == copied_before,'Copied release bytes/modes/mtimes changed: '+check['label'])
                verify_identity(work)
            modes[mode] = records
    typed_equal(modes['normal'],modes['optimized'],'normal/optimized replay')
    regression = semantic_regression()
    need(snapshot(ROOT) == before,'Original release bytes/modes/mtimes changed during replay')
    verify_identity()
    return {'schema':'report37-replay-v1','status':'PASS','manifest_sha256':MANIFEST_SHA256,'release_stage':manifest['release_stage'],'identity_verified_before_copied_execution':True,'fresh_external_copies':2,'normal_optimized_receipt_bytes_equal':True,'original_and_copied_bytes_modes_mtimes_preserved':True,'upstream_sources_executed':False,'mathematical_executables':sorted(MATH_SCRIPTS),'strict_receipt_regression':regression,'modes':modes,'scope':'Finite exact corroboration and exclusions; no full negative compiler zero and no unbounded positivity result.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--verify-only',action='store_true')
    group.add_argument('--self-test-types',action='store_true')
    group.add_argument('--replay',action='store_true')
    parser.add_argument('--workdir',help='external parent for disposable replay copies')
    args = parser.parse_args()
    need(args.replay or args.workdir is None, '--workdir requires --replay')
    if args.self_test_types:
        result = semantic_regression()
    elif args.verify_only:
        doc,_ = verify_identity()
        result = {'schema':'report37-identity-v1','status':'PASS','manifest_sha256':MANIFEST_SHA256,'release_stage':doc['release_stage'],'file_count':doc['file_count']}
    else:
        result = full_replay(args.workdir)
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__ == '__main__':
    try:main()
    except (RuntimeError,OSError,ValueError,SyntaxError,RecursionError,subprocess.SubprocessError) as exc:
        print(str(exc),file=sys.stderr)
        raise SystemExit(1)
