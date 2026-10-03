#!/usr/bin/env python3
"""Strict, identity-gated Report35 replay. All execution occurs in external copies.

This validates sealed bytes and bounded authored checks, not the universal theorem.
The independently supplied ZIP or manifest digest remains the authenticity anchor.
"""
import argparse
import ast
import hashlib
import json
import math
import os
from pathlib import Path, PurePosixPath
import re
import runpy
import shutil
import stat
import subprocess
import sys
import tempfile

MANIFEST_SHA256 = "7d55c5edf03583a08d38efe123b6922969acc5cf62fd8b975da376a2d621653f"
ROOT = Path(__file__).resolve().parent
PIN_PATTERN = rb'(?m)^MANIFEST_SHA256 = "[0-9a-f]{64}"$'
ZERO_PIN_LINE = b'MANIFEST_SHA256 = "' + b'0'*64 + b'"'
HASH_CONVENTION = 'sha256; verify_release.py self-pin line normalized to 64 zeros; all other files byte-exact'
LOADER_FROZEN_PIN = 'de3e161de813afb098110223f9850c49cb8bcd481af69f8b9789daa3ca2950e3'
LOADER_AUDIT_PIN = '2e8097792099a7b6aaca04f29b27b14c47a3e374a7608b440cd78b288f10e499'
TABLE_PIN = '0c6d8ae506f503e2783f6ed2ee68db4cde2f501b9864f376ab3773f86b59428a'
COMPOSITION_FROZEN_PIN = '6ef864b071230afeb03f26ab27e4eb39c38f4c9a0410cd32b7daa262a26e65c6'
COMPOSITION_AUDIT_PIN = '7f1e9a13e61dec92e02862324a23b286e05bb22ac862a8cf0ee5df09db29893d'


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


def verify_identity(root=ROOT):
    need(MANIFEST_SHA256 != '0'*64, 'Identity gate: release is not sealed')
    before = snapshot(root)
    raw = (root/'MANIFEST.json').read_bytes()
    need(sha(raw) == MANIFEST_SHA256, 'Identity gate: enclosing manifest digest mismatch')
    doc = parse_json(raw, 'manifest')
    need(type(doc) is dict and set(doc) == {'schema', 'release_stage', 'files', 'file_count', 'hash_convention'}, 'Identity gate: manifest shape')
    need(doc['schema'] == 'report35-release-inventory-v1', 'Identity gate: manifest schema')
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
        need({'Research_Report35.tex', 'Research_Report35.pdf'} <= set(files), 'Identity gate: final article missing')
        need(any(n.startswith('evidence/composition/') for n in files), 'Identity gate: approved composition missing')
    for name in files:
        p = root/name
        if p.suffix == '.py':
            need(not any(isinstance(n, ast.Assert) for n in ast.walk(ast.parse(p.read_bytes()))), 'Identity gate: optimization-disabled assertion: ' + name)
        if p.suffix == '.json':
            read_json(p)
        if p.suffix in ('.py', '.json', '.md', '.tex', '.sh', '.txt', '.out'):
            raw = p.read_bytes()
            for prefix in (b'/' + b'workspace/', b'/' + b'home/', b'/' + b'root/', b'/' + b'tmp/'):
                need(prefix not in raw, 'Identity gate: private absolute path: ' + name)
    for name, digest in [('FROZEN-INPUTS.json', LOADER_FROZEN_PIN), ('INDEPENDENT-AUDIT.md', LOADER_AUDIT_PIN), ('data/u15_table.json', TABLE_PIN)]:
        need(sha((root/'evidence/loader'/name).read_bytes()) == digest, 'Identity gate: approved loader pin mismatch')
    frozen = read_json(root/'evidence/loader/FROZEN-INPUTS.json')
    for name, record in frozen['files'].items():
        safe_relative(name)
        raw = (root/'evidence/loader'/name).read_bytes()
        typed_equal({'bytes':len(raw), 'sha256':sha(raw)}, record, 'approved loader frozen entry')
    if (root/'evidence/composition').is_dir():
        for name,digest in [('FROZEN-INPUTS.json',COMPOSITION_FROZEN_PIN),('review/INDEPENDENT_AUDIT.md',COMPOSITION_AUDIT_PIN)]:
            need(sha((root/'evidence/composition'/name).read_bytes()) == digest, 'Identity gate: approved composition pin mismatch')
        composition = read_json(root/'evidence/composition/FROZEN-INPUTS.json')
        for name,record in composition['files'].items():
            safe_relative(name)
            raw = (root/'evidence/composition'/name).read_bytes()
            typed_equal({'bytes':len(raw),'sha256':sha(raw)},record,'approved composition frozen entry')
        typed_equal(read_json(root/'evidence/composition/verification.json'),read_json(root/'evidence/composition/verification_optimized.json'),'frozen composition normal/optimized receipts')
    lineage = read_json(root/'verification/source-lineage.json')
    need(type(lineage) is dict and set(lineage) == {'schema','files'} and lineage['schema'] == 'report35-source-lineage-v1', 'Identity gate: lineage shape')
    need(type(lineage['files']) is list, 'Identity gate: lineage list type')
    mapped = set()
    for row in lineage['files']:
        need(type(row) is dict and set(row) == {'packet','original_relative_path','packaged_relative_path','original_sha256','packaged_sha256','normalization'}, 'Identity gate: lineage entry shape')
        name = row['packaged_relative_path'];safe_relative(name);safe_relative(row['original_relative_path'])
        need(name in files and name.startswith('evidence/') and name not in mapped, 'Identity gate: lineage target mismatch')
        mapped.add(name)
        need(row['normalization'] == 'none; byte-exact', 'Identity gate: unexpected evidence normalization')
        need(row['original_sha256'] == row['packaged_sha256'] == sha((root/name).read_bytes()), 'Identity gate: evidence lineage digest mismatch')
        need(type(row['packet']) is str and row['packet'] in ('literal-sandpile-loader-20261003','sandpile-certificate-composition-20261003'), 'Identity gate: source packet name')
    need(mapped == {name for name in files if name.startswith('evidence/')}, 'Identity gate: incomplete evidence lineage')
    expected = read_json(root/'verification/expected-receipts.json')
    need(type(expected) is dict and len(expected) >= 7, 'Identity gate: expected receipt inventory')
    for name, receipt in expected.items():
        safe_relative(name)
        need(name in files, 'Identity gate: unchecked expected receipt')
        typed_equal(read_json(root/name), receipt, 'stored ' + name)
    plan = read_json(root/'verification/replay-plan.json')
    need(type(plan) is dict and set(plan) == {'schema','checks'} and plan['schema'] == 'report35-replay-plan-v1', 'Identity gate: replay plan shape')
    need(type(plan['checks']) is list and len(plan['checks']) >= 6, 'Identity gate: replay checks')
    labels = set()
    for check in plan['checks']:
        need(type(check) is dict and set(check) == {'label','script','cwd','args','receipt','capture'}, 'Identity gate: replay check shape')
        for key in ('label','script','cwd','receipt','capture'):
            need(type(check[key]) is str, 'Identity gate: check string type')
        need(check['label'] not in labels, 'Identity gate: duplicate check label')
        labels.add(check['label'])
        need(type(check['args']) is list and all(type(v) is str for v in check['args']), 'Identity gate: check arguments')
        need(check['capture'] in ('file','stdout'), 'Identity gate: capture kind')
        for key in ('script','cwd','receipt'):safe_relative(check[key])
        need(check['script'] in files and check['cwd'] in dirs and check['receipt'] in expected, 'Identity gate: unchecked replay dependency')
    return doc, before


def semantic_regression():
    cases = [(True,1),(False,0),(1,True),(1.0,1),({'n':True},{'n':1}),({'sos':False},{'sos':0}),([False],[0]),({'n':1,'extra':0},{'n':1}),({},{'n':1}),([1],[1,2]),(None,0),('1',1),({'a':[{'n':True}]},{'a':[{'n':1}]})]
    for a,b in cases:
        try:typed_equal(a,b)
        except RuntimeError:pass
        else:raise RuntimeError('Strict comparator accepted a mutation')
    malformed = ['{"x":1,"x":1}', '{"n":NaN}', '{"n":Infinity}', '{"n":-Infinity}', '{"n":1e9999}', '{', '[1,]', '{"n":01}', b'\xff']
    for raw in malformed:
        try:parse_json(raw)
        except RuntimeError:pass
        else:raise RuntimeError('Strict parser accepted malformed JSON')
    valid = {'ok':True,'count':1,'zero':0,'x':[None,'a',1.5]}
    typed_equal(parse_json(json.dumps(valid)),valid)
    return {'status':'PASS','typed_mutations_rejected':len(cases),'malformed_json_rejected':len(malformed)}


BOOTSTRAP = "import pathlib,runpy,sys; p=pathlib.Path(sys.argv[1]).resolve(); sys.path.insert(0,str(p.parent)); sys.argv=sys.argv[1:]; runpy.run_path(str(p),run_name='__main__')"


def full_replay(work_parent=None):
    manifest,before = verify_identity()
    expected = read_json(ROOT/'verification/expected-receipts.json')
    plan = read_json(ROOT/'verification/replay-plan.json')['checks']
    if work_parent is not None:
        work_parent = Path(work_parent).resolve()
        need(work_parent != ROOT and ROOT not in work_parent.parents, 'Replay directory must be external')
        work_parent.mkdir(parents=True,exist_ok=True)
    env = {k:v for k,v in os.environ.items() if not k.startswith('PYTHON')}
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    modes = {}
    for mode,optimized in [('normal',False),('optimized',True)]:
        with tempfile.TemporaryDirectory(prefix='report35-'+mode+'-', dir=work_parent) as tmp:
            work = Path(tmp)/'relocated-release'
            shutil.copytree(ROOT,work,copy_function=shutil.copy2)
            verify_identity(work)
            records = {}
            for check in plan:
                target = work/check['receipt']
                # Removing only the copied expected output proves it is recreated.
                target.unlink()
                cmd = [sys.executable,'-I','-B'] + (['-O'] if optimized else []) + ['-c',BOOTSTRAP,str(work/check['script'])] + check['args']
                result = subprocess.run(cmd,cwd=work/check['cwd'],env=env,text=True,capture_output=True,timeout=1800)
                need(result.returncode == 0,'Replay failed: ' + check['label'] + ': ' + result.stderr[-3000:])
                need(not result.stderr.strip(),'Unexpected replay stderr: ' + check['label'])
                if check['capture'] == 'stdout':
                    target.write_text(result.stdout,encoding='utf-8')
                need(target.is_file() and not target.is_symlink(),'Replay receipt was not regenerated: '+check['label'])
                receipt = read_json(target)
                typed_equal(receipt,expected[check['receipt']],check['label']+' '+mode)
                # Every overwritten receipt must also be byte-identical to its frozen source.
                need(target.read_bytes() == (ROOT/check['receipt']).read_bytes(),'Replay receipt byte inequality: '+check['label'])
                records[check['label']] = {'status':'PASS','receipt_sha256':sha(target.read_bytes()),'stdout_sha256':sha(result.stdout.encode())}
                # Restore the frozen receipt mode after fresh creation (independent of umask).
                target.chmod(manifest['files'][check['receipt']]['mode'])
                # Re-establish every code/data identity before the next producer.
                verify_identity(work)
            modes[mode] = records
    typed_equal(modes['normal'],modes['optimized'],'normal/optimized replay')
    regression = semantic_regression()
    need(snapshot(ROOT) == before,'Original release bytes/modes/mtimes changed during replay')
    verify_identity()
    return {'schema':'report35-replay-v1','status':'PASS','manifest_sha256':MANIFEST_SHA256,'release_stage':manifest['release_stage'],'identity_verified_before_copied_execution':True,'fresh_external_copies':2,'normal_optimized_receipts_and_stdout_equal':True,'original_bytes_modes_mtimes_preserved':True,'strict_receipt_regression':regression,'modes':modes,'scope':'Bounded authored evidence and release integrity; the infinite construction and certificate theorems require the accompanying proofs.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--verify-only',action='store_true')
    group.add_argument('--self-test-types',action='store_true')
    group.add_argument('--replay',action='store_true')
    parser.add_argument('--workdir',help='external parent for disposable replay copies')
    args = parser.parse_args()
    if args.self_test_types:
        result = semantic_regression()
    elif args.verify_only:
        doc,_ = verify_identity()
        result = {'schema':'report35-identity-v1','status':'PASS','manifest_sha256':MANIFEST_SHA256,'release_stage':doc['release_stage'],'file_count':doc['file_count']}
    else:
        result = full_replay(args.workdir)
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__ == '__main__':
    try:main()
    except (RuntimeError,OSError,ValueError,SyntaxError,subprocess.SubprocessError) as exc:
        print(str(exc),file=sys.stderr)
        raise SystemExit(1)
