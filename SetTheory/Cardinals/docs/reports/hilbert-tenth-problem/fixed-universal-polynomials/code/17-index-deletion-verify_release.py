#!/usr/bin/env python3
"""Strict, identity-gated Report41 replay in fresh external copies.

This authenticates a release and reproduces finite checks, not a substitute for the symbolic
full-counterfamily theorem. Authenticate the complete archive with a trusted external hash
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

MANIFEST_SHA256 = "5baea7d2505e168b6a3c45f8ddcdd697463e765e16a166ea67ab1333f56394f1"
ROOT = Path(__file__).resolve().parent
PIN_PATTERN = rb'(?m)^MANIFEST_SHA256 = "[0-9a-f]{64}"$'
ZERO_PIN_LINE = b'MANIFEST_SHA256 = "' + b'0'*64 + b'"'
HASH_CONVENTION = 'sha256; verify_release.py self-pin line normalized to 64 zeros; all other files byte-exact'
SOURCE_MANIFEST_PIN = '94f45847037067162dd21e77f19e8edc2cc53cb0aa9ca6642e335c5d7c21cbb4'
SMOOTH_MANIFEST_PIN = 'ac48a5a3206514ac1b49d8bb510807e351fccf11730952f19c827b916f28f82b'
SMOOTH_PROOF_PIN = '259ec165067555228eb97fd6ca37180feaba6861df4ce1cce94d73917b12d8ca'
PROOF_PIN = 'dc886e8991e32c331b9135b4ea6b3f73733656be3df6c2aa01576e1732fb83e1'
MATH_SCRIPTS = {'evidence/check_reduction.py': 'd8abf86c2179d4fad8bab0af719dda1c2120a0f6c09dc958cd9885052cec576e', 'evidence/check_full_counterfamily.py': 'becd5f392f73e594a8d300ab183dfda1e310ec90d2ab4103170fbb2787368cf2', 'evidence/audit_bootstrap/check_bootstrap.py': 'b7b78b57cfd2be74d8d0a924a7ce5f46a31ae54ec067a026d44c348d1bfccc7b', 'evidence/audit_bootstrap/check_counterfamily.py': '4a7da526e33a469006c4ebe56cc7422333ec7491d8d378b0b48e115f13ae75cd', 'smooth/check_smooth_radix.py': 'fce6a0113e79c1134a94b4ac9b668d5cf88e83a3f4198d8b90e882c0dcaa2e7a'}
CHECKS = [{'label': 'authored-reduction', 'script': 'evidence/check_reduction.py', 'receipt': 'evidence/CHECKS.json', 'expected': 'evidence/CHECKS.json', 'capture': 'stdout'}, {'label': 'authored-full-counterfamily', 'script': 'evidence/check_full_counterfamily.py', 'receipt': 'evidence/FULL_CHECKS.json', 'expected': 'evidence/FULL_CHECKS.json', 'capture': 'stdout'}, {'label': 'reviewer-bootstrap-author-replay', 'script': 'evidence/audit_bootstrap/check_bootstrap.py', 'receipt': 'evidence/audit_bootstrap/bootstrap_release_replay.json', 'expected': 'evidence/audit_bootstrap/bootstrap_release_replay.json', 'capture': 'stdout'}, {'label': 'reviewer-counterfamily-author-replay', 'script': 'evidence/audit_bootstrap/check_counterfamily.py', 'receipt': 'evidence/audit_bootstrap/counterfamily_release_replay.json', 'expected': 'evidence/audit_bootstrap/counterfamily_release_replay.json', 'capture': 'stdout'}, {'label': 'smooth-radix-author-checks', 'script': 'smooth/check_smooth_radix.py', 'receipt': 'smooth/CHECKS.json', 'expected': 'smooth/CHECKS.json', 'capture': 'stdout'}]

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
    review = read_json(root/'verification/release-review.json')
    need(type(review) is dict and review.get('schema') == 'report41-release-review-v1' and review.get('status') == 'APPROVED', 'Identity gate: final release approval missing')
    need(review.get('source_manifest_sha256') == SOURCE_MANIFEST_PIN and review.get('proof_sha256') == PROOF_PIN, 'Identity gate: release approval source mismatch')
    need(review.get('smooth_manifest_sha256') == SMOOTH_MANIFEST_PIN and review.get('smooth_proof_sha256') == SMOOTH_PROOF_PIN, 'Identity gate: smooth approval mismatch')
    need(review.get('all_page_visual_qa') is True, 'Identity gate: all-page visual approval missing')
    for suffix in ('tex','pdf'):
        need(review.get('article_'+suffix+'_sha256') == sha((root/('Research_Report41.'+suffix)).read_bytes()), 'Identity gate: article approval mismatch: '+suffix)


def verify_identity(root=ROOT):
    need(MANIFEST_SHA256 != '0'*64, 'Identity gate: release is not sealed')
    before = snapshot(root)
    raw = (root/'MANIFEST.json').read_bytes()
    need(sha(raw) == MANIFEST_SHA256, 'Identity gate: enclosing manifest digest mismatch')
    doc = parse_json(raw, 'Identity gate: manifest')
    need(type(doc) is dict and set(doc) == {'schema', 'release_stage', 'files', 'file_count', 'hash_convention'}, 'Identity gate: manifest shape')
    need(doc['schema'] == 'report41-release-inventory-v1', 'Identity gate: manifest schema')
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
        need({'Research_Report41.tex', 'Research_Report41.pdf'} <= set(files), 'Identity gate: final article missing')
        verify_approval(root)
    for name in files:
        p = root/name
        # Upstream source programs are preserved as inert bytes, not parsed or run.
        if p.suffix == '.py' and (not name.startswith(('evidence/','smooth/')) or name in MATH_SCRIPTS):
            need(not any(isinstance(n, ast.Assert) for n in ast.walk(ast.parse(p.read_bytes()))), 'Identity gate: optimization-disabled assertion: ' + name)
        if p.suffix == '.json':
            read_json(p)
        if not name.startswith(('evidence/','smooth/')) and p.suffix in ('.py', '.json', '.md', '.tex', '.sh', '.txt'):
            raw = p.read_bytes()
            for prefix in (b'/' + b'workspace/', b'/' + b'home/', b'/' + b'root/'):
                need(prefix not in raw, 'Identity gate: private absolute path: ' + name)
    source = root/'evidence'
    source_raw = (source/'MANIFEST.json').read_bytes()
    need(sha(source_raw) == SOURCE_MANIFEST_PIN, 'Identity gate: frozen source manifest pin mismatch')
    source_doc = parse_json(source_raw, 'Identity gate: frozen source manifest')
    need(type(source_doc) is dict and type(source_doc.get('files')) is list, 'Identity gate: frozen source manifest shape')
    source_names = {'MANIFEST.json'}
    need(len(source_doc['files']) == 48, 'Identity gate: frozen source file count')
    for row in source_doc['files']:
        need(type(row) is dict and set(row) == {'path','bytes','sha256'}, 'Identity gate: frozen source entry shape')
        name=row['path']; safe_relative(name)
        need(name not in source_names, 'Identity gate: duplicate/recursive source entry')
        source_names.add(name)
        raw=(source/name).read_bytes()
        need(type(row['bytes']) is int and len(raw)==row['bytes'] and sha(raw)==row['sha256'], 'Identity gate: frozen source bytes changed: '+name)
    need({n for n in files if n.startswith('evidence/')} == {'evidence/'+n for n in source_names}, 'Identity gate: source inventory differs from frozen 49-file packet')
    need(sha((source/'FULL_COUNTERFAMILY.md').read_bytes()) == PROOF_PIN, 'Identity gate: proof pin mismatch')
    for name,digest in MATH_SCRIPTS.items():
        need(sha((root/name).read_bytes()) == digest, 'Identity gate: mathematical executable pin mismatch')
    lineage={'schema':'report41-source-lineage-v1','inventory_authority':'frozen source MANIFEST.json; 48 payload files plus the manifest','source_manifest_sha256':SOURCE_MANIFEST_PIN,'normalization':'none; all members copied byte-exactly','files':[]}
    for name in sorted(source_names):
        lineage['files'].append({'original_relative_path':name,'packaged_relative_path':'evidence/'+name,'sha256':sha((source/name).read_bytes())})
    typed_equal(read_json(root/'verification/source-lineage.json'),lineage,'Identity gate: exact source lineage')
    smooth = root/'smooth'
    raw=(smooth/'MANIFEST.json').read_bytes()
    need(sha(raw)==SMOOTH_MANIFEST_PIN,'Identity gate: frozen smooth manifest pin mismatch')
    sm=parse_json(raw,'Identity gate: smooth manifest')
    need(type(sm) is dict and type(sm.get('files')) is list and len(sm['files'])==8,'Identity gate: smooth manifest shape/count')
    need(sm.get('original_factorial_manifest_sha256')==SOURCE_MANIFEST_PIN and sm.get('original_factorial_full_proof_sha256')==PROOF_PIN,'Identity gate: smooth factorial provenance mismatch')
    smooth_names={'MANIFEST.json'}
    for row in sm['files']:
        need(type(row) is dict and set(row)=={'path','bytes','sha256'},'Identity gate: smooth entry shape')
        name=row['path'];safe_relative(name)
        need(name not in smooth_names,'Identity gate: duplicate/recursive smooth entry')
        smooth_names.add(name);raw=(smooth/name).read_bytes()
        need(type(row['bytes']) is int and len(raw)==row['bytes'] and sha(raw)==row['sha256'],'Identity gate: smooth frozen bytes changed: '+name)
    need({n for n in files if n.startswith('smooth/')}=={'smooth/'+n for n in smooth_names},'Identity gate: smooth exact inventory mismatch')
    need(sha((smooth/'SMOOTH_RADIX.md').read_bytes())==SMOOTH_PROOF_PIN,'Identity gate: smooth proof pin mismatch')
    smooth_lineage={'schema':'report41-smooth-lineage-v1','inventory_authority':'separately frozen smooth MANIFEST.json; 8 payload files plus the manifest','source_manifest_sha256':SMOOTH_MANIFEST_PIN,'normalization':'none; all members copied byte-exactly','attribution':'root/author reviewed optional corollary; original independent audit is not relabeled','files':[]}
    for name in sorted(smooth_names):
        smooth_lineage['files'].append({'original_relative_path':name,'packaged_relative_path':'smooth/'+name,'sha256':sha((smooth/name).read_bytes())})
    typed_equal(read_json(root/'verification/smooth-lineage.json'),smooth_lineage,'Identity gate: exact smooth lineage')
    expected = read_json(root/'verification/expected-receipts.json')
    need(type(expected) is dict and set(expected) == {c['receipt'] for c in CHECKS}, 'Identity gate: expected receipt inventory')
    for check in CHECKS:
        typed_equal(read_json(root/check['receipt']), expected[check['receipt']], 'Identity gate: stored '+check['receipt'])
        typed_equal(read_json(root/check['expected']), expected[check['receipt']], 'Identity gate: expected '+check['expected'])
        need((root/check['receipt']).read_bytes() == (root/check['expected']).read_bytes(), 'Identity gate: stored/expected receipt bytes differ')
    typed_equal(read_json(root/'verification/replay-plan.json'), {'schema':'report41-replay-plan-v1','runtime':'Python 3.9+ standard library only','checks':CHECKS}, 'Identity gate: exact replay plan')
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
    return {'python_minimum':'3.9','dependencies':'standard library only','automatic_installation':False}


def receipt_directory(value):
    if value is None:
        return None
    path = Path(value).resolve()
    need(path != ROOT and ROOT not in path.parents, 'Receipt directory must be external')
    need(not path.exists() and not Path(value).is_symlink(), 'Receipt directory must be new; existing paths are never overwritten')
    need(path.parent.is_dir(), 'Receipt directory parent must already exist')
    return path


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
        with tempfile.TemporaryDirectory(prefix='report41-'+mode+'-', dir=work_parent) as tmp:
            work = Path(tmp)/'relocated-release'
            shutil.copytree(ROOT,work,copy_function=shutil.copy2)
            _,copied_before = verify_identity(work)
            records = {}
            for check in CHECKS:
                # Authenticated authored scripts print fresh receipts; no source
                # receipt is opened for writing, and no upstream program executes.
                need(check['script'] in MATH_SCRIPTS, 'Replay executable is not allowlisted')
                program = work/check['script']
                cmd = [sys.executable,'-I','-B'] + (['-O'] if optimized else []) + [str(program),'--expect',str(work/check['expected'])]
                result = subprocess.run(cmd,cwd=Path(tmp),env=env,capture_output=True,timeout=1800)
                need(result.returncode == 0,'Replay failed: ' + check['label'] + ': ' + result.stderr[-3000:].decode('utf-8','replace'))
                need(not result.stderr.strip(),'Unexpected replay stderr: ' + check['label'])
                receipt = parse_json(result.stdout, check['label']+' '+mode)
                typed_equal(receipt,expected[check['receipt']],check['label']+' '+mode)
                need(result.stdout == (ROOT/check['receipt']).read_bytes(),'Replay receipt byte inequality: '+check['label'])
                exports[mode+'-'+check['label']+'.json'] = result.stdout
                records[check['label']] = {'status':'PASS','receipt_sha256':sha(result.stdout),'stdout_bytes':len(result.stdout)}
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
    return {'schema':'report41-replay-v1','runtime':runtime,'external_receipts_exported':destination is not None,'status':'PASS','manifest_sha256':MANIFEST_SHA256,'release_stage':manifest['release_stage'],'identity_verified_before_copied_execution':True,'fresh_external_copies':2,'normal_optimized_receipt_bytes_equal':True,'original_and_copied_bytes_modes_mtimes_preserved':True,'upstream_sources_executed':False,'mathematical_executables':sorted(MATH_SCRIPTS),'strict_receipt_regression':regression,'modes':modes,'scope':'Exact newly authored component checks and inert structural source inspection corroborate a separate symbolic full-counterfamily proof. No upstream code, saved arithmetic schedule, or full astronomical witness tuple is executed or materialized. Original independent review attribution is preserved; hardened reviewer-written checkers are author-attributed replays. Bound 85 is unchanged.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--verify-only',action='store_true')
    group.add_argument('--self-test-types',action='store_true')
    group.add_argument('--replay',action='store_true')
    parser.add_argument('--workdir',help='external parent for disposable replay copies')
    parser.add_argument('--receipt-dir',help='new external directory for ten fresh stdout receipts; parent must exist')
    args = parser.parse_args()
    need(args.replay or (args.workdir is None and args.receipt_dir is None), '--workdir and --receipt-dir require --replay')
    if args.self_test_types:
        result = semantic_regression()
    elif args.verify_only:
        doc,_ = verify_identity()
        result = {'schema':'report41-identity-v1','status':'PASS','manifest_sha256':MANIFEST_SHA256,'release_stage':doc['release_stage'],'file_count':doc['file_count']}
    else:
        result = full_replay(args.workdir,args.receipt_dir)
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__ == '__main__':
    try:main()
    except (RuntimeError,OSError,ValueError,SyntaxError,RecursionError,subprocess.SubprocessError) as exc:
        print(str(exc),file=sys.stderr)
        raise SystemExit(1)
