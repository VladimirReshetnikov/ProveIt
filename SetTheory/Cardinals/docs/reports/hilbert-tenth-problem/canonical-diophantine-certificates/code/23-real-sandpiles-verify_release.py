#!/usr/bin/env python3
"""Strict, identity-gated Report36 replay. All execution occurs in external copies.

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

MANIFEST_SHA256 = "237e4c298ed934addc2313dda767216c60053f541dfe7c79a33caf20bbf0d020"
ROOT = Path(__file__).resolve().parent
PIN_PATTERN = rb'(?m)^MANIFEST_SHA256 = "[0-9a-f]{64}"$'
ZERO_PIN_LINE = b'MANIFEST_SHA256 = "' + b'0'*64 + b'"'
HASH_CONVENTION = 'sha256; verify_release.py self-pin line normalized to 64 zeros; all other files byte-exact'
SOURCE_MANIFEST_PIN = '99e4371291d46d7ee8ef4821254ad702791e9b84060e69336d652e603c059ee1'
SOURCE_SUMS_PIN = '989475cde0bd3432fdab444822c6dfd137d79e8d5915fb704b5b2068ddc6ebb8'
BASE_COMPILER_PIN = 'bf22889eebe546593e933c120c72efb95e5504e6e2ab7d2bc10da4a5dd6623a2'
BASE_PROOF_PIN = '6e5a053e7f599a17ee77c49e3092e041c7ea3e0de62156095fe9ece5e761d60e'
SYMPY_VERSION = '1.14.0'


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
    need(doc['schema'] == 'report36-release-inventory-v1', 'Identity gate: manifest schema')
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
        need({'Research_Report36.tex', 'Research_Report36.pdf'} <= set(files), 'Identity gate: final article missing')
        verify_release_approval(root)
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
    # Authenticate the complete source packet before any payload code is imported.
    source = root/'evidence/real'
    need(sha((source/'MANIFEST.json').read_bytes()) == SOURCE_MANIFEST_PIN, 'Identity gate: frozen source manifest pin mismatch')
    need(sha((source/'SHA256SUMS').read_bytes()) == SOURCE_SUMS_PIN, 'Identity gate: frozen source sums pin mismatch')
    frozen = read_json(source/'MANIFEST.json')
    need(type(frozen) is dict and set(frozen) == {'schema','purpose','files'}, 'Identity gate: source manifest shape')
    need(type(frozen['schema']) is int and frozen['schema'] == 1 and type(frozen['purpose']) is str, 'Identity gate: source metadata')
    need(type(frozen['files']) is list and len(frozen['files']) == 16, 'Identity gate: frozen source file count')
    source_names = set()
    for row in frozen['files']:
        need(type(row) is dict and set(row) == {'path','bytes','sha256'}, 'Identity gate: source entry shape')
        name = row['path'];safe_relative(name)
        need(name not in source_names and name not in ('MANIFEST.json','SHA256SUMS'), 'Identity gate: duplicate source entry')
        source_names.add(name)
        raw = (source/name).read_bytes()
        typed_equal({'bytes':len(raw),'sha256':sha(raw)}, {'bytes':row['bytes'],'sha256':row['sha256']}, 'Identity gate: frozen source entry '+name)
    source_names.update(('MANIFEST.json','SHA256SUMS'))
    need({name for name in files if name.startswith('evidence/')} == {'evidence/real/'+n for n in source_names}, 'Identity gate: source inventory is not the exact frozen 18-file packet')
    expected_sums = ''.join(sha((source/n).read_bytes())+'  '+n+'\n' for n in sorted(source_names-{'SHA256SUMS'}))
    need((source/'SHA256SUMS').read_text(encoding='utf-8') == expected_sums, 'Identity gate: frozen source checksum inventory mismatch')
    for name,digest in [('approved_base/prism_certificate.py',BASE_COMPILER_PIN),('approved_base/PROOF.md',BASE_PROOF_PIN)]:
        need(sha((source/name).read_bytes()) == digest, 'Identity gate: approved predecessor context pin mismatch')
    lineage = read_json(root/'verification/source-lineage.json')
    need(type(lineage) is dict and set(lineage) == {'schema','inventory_authority','files'} and lineage['schema'] == 'report36-source-lineage-v1', 'Identity gate: lineage shape')
    need(type(lineage['inventory_authority']) is str and type(lineage['files']) is list and len(lineage['files']) == 18, 'Identity gate: lineage metadata')
    mapped = set()
    for row in lineage['files']:
        need(type(row) is dict and set(row) == {'packet','original_relative_path','packaged_relative_path','original_sha256','packaged_sha256','normalization','role'}, 'Identity gate: lineage entry shape')
        name = row['packaged_relative_path'];original = row['original_relative_path']
        safe_relative(name);safe_relative(original)
        need(name == 'evidence/real/'+original and original in source_names and name not in mapped, 'Identity gate: lineage target mismatch')
        mapped.add(name)
        need(row['normalization'] == 'none; byte-exact', 'Identity gate: unexpected evidence normalization')
        need(row['original_sha256'] == row['packaged_sha256'] == sha((root/name).read_bytes()), 'Identity gate: evidence lineage digest mismatch')
        need(row['packet'] == 'real-sandpile-certificate-20261003', 'Identity gate: source packet name')
        role = 'selected predecessor context; not the complete Report35 packet' if original.startswith('approved_base/') else 'complete frozen real-strengthening packet member'
        need(row['role'] == role, 'Identity gate: source context role')
    need(mapped == {name for name in files if name.startswith('evidence/')}, 'Identity gate: incomplete evidence lineage')
    expected = read_json(root/'verification/expected-receipts.json')
    receipt_names = {'evidence/real/'+name for name in ('verification.json','verification_optimized.json','independent_coefficient_ledger_receipt.json','independent_coefficient_ledger_receipt_optimized.json')}
    need(type(expected) is dict and set(expected) == receipt_names, 'Identity gate: exact expected receipt inventory')
    for name,receipt in expected.items():
        need(name in files, 'Identity gate: unchecked expected receipt')
        typed_equal(read_json(root/name), receipt, 'stored '+name)
    for a,b in [('verification.json','verification_optimized.json'),('independent_coefficient_ledger_receipt.json','independent_coefficient_ledger_receipt_optimized.json')]:
        typed_equal(read_json(source/a),read_json(source/b),'frozen normal/optimized receipts')
        need((source/a).read_bytes() == (source/b).read_bytes(), 'Identity gate: frozen normal/optimized receipt bytes differ')
    plan = read_json(root/'verification/replay-plan.json')
    checks = []
    for label,script,receipt in [('main-exact-checks','exact_checks.py','verification.json'),('independent-coefficient-ledger','independent_coefficient_ledger_checks.py','independent_coefficient_ledger_receipt.json')]:
        checks.append({'label':label,'script':'evidence/real/'+script,'cwd':'evidence/real','args':['--output',receipt],'receipt':'evidence/real/'+receipt,'capture':'file'})
    typed_equal(plan,{'schema':'report36-replay-plan-v1','required_sympy':SYMPY_VERSION,'checks':checks},'Identity gate: exact replay plan')
    return doc, before


def verify_release_approval(root):
    p = root/'verification/release-review.json'
    need(p.is_file(), 'Identity gate: final release approval record missing')
    review = read_json(p)
    need(type(review) is dict and {'schema','status','source_manifest_sha256','source_base_compiler_sha256'} <= set(review), 'Identity gate: release review shape')
    need(review['schema'] == 'report36-release-review-v1' and review['status'] == 'APPROVED', 'Identity gate: release review is not approved')
    need(review['source_manifest_sha256'] == SOURCE_MANIFEST_PIN and review['source_base_compiler_sha256'] == BASE_COMPILER_PIN, 'Identity gate: release approval source identity mismatch')


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
    preflight = subprocess.run([sys.executable,'-I','-B','-c',"import sympy; print(sympy.__version__)"],env=env,text=True,capture_output=True,timeout=120)
    need(preflight.returncode == 0 and not preflight.stderr.strip() and preflight.stdout.strip() == SYMPY_VERSION, 'Replay requires installed SymPy '+SYMPY_VERSION+'; no installation is performed')
    modes = {}
    for mode,optimized in [('normal',False),('optimized',True)]:
        with tempfile.TemporaryDirectory(prefix='report36-'+mode+'-', dir=work_parent) as tmp:
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
    return {'schema':'report36-replay-v1','status':'PASS','manifest_sha256':MANIFEST_SHA256,'release_stage':manifest['release_stage'],'identity_verified_before_copied_execution':True,'fresh_external_copies':2,'normal_optimized_receipts_and_stdout_equal':True,'original_bytes_modes_mtimes_preserved':True,'required_sympy':SYMPY_VERSION,'strict_receipt_regression':regression,'modes':modes,'scope':'Bounded authored evidence and release integrity; the infinite construction and certificate theorems require the accompanying proofs.'}


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
        result = {'schema':'report36-identity-v1','status':'PASS','manifest_sha256':MANIFEST_SHA256,'release_stage':doc['release_stage'],'file_count':doc['file_count']}
    else:
        result = full_replay(args.workdir)
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__ == '__main__':
    try:main()
    except (RuntimeError,OSError,ValueError,SyntaxError,RecursionError,subprocess.SubprocessError) as exc:
        print(str(exc),file=sys.stderr)
        raise SystemExit(1)
