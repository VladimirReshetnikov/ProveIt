#!/usr/bin/env python3
"""Identity-gated Report38 replay of the frozen one-visit observation packet.

Authenticate the complete release archive with a trusted external hash tool
before running any packaged program. A self-reported PASS is not a trust anchor.
Only the active author/independent tests and example execute; prior context and
the source packet verifier are preserved as inert bytes.
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

MANIFEST_SHA256 = "115cf44fb4f42f346fdb45319b13edbda0dc5251aac02cc17e541ba0df77d79c"
ROOT = Path(__file__).resolve().parent
PIN_PATTERN = rb'(?m)^MANIFEST_SHA256 = "[0-9a-f]{64}"$'
ZERO_PIN_LINE = b'MANIFEST_SHA256 = "' + b'0'*64 + b'"'
HASH_CONVENTION = 'sha256; verify_release.py self-pin line normalized to 64 zeros; all other files byte-exact'
SOURCE_MANIFEST_PIN = '7dfd4f270ad7bf667bc123aace7bd97fd13b992949a9dfc8e3dca3f8105cea62'
PROOF_PIN = 'd4fa1ecec1b80d320a36ee464095c38fe671531757cc5dfcb85c3f8b62e30f12'
SOURCE_PREFIX = 'evidence/source-packet/'
ACTIVE_PROGRAMS = {
    'one_visit.py': '6b2bc54678a5a4c18db8eec23e37195a3c526d7f152863a1fb3a1f8d682429f7',
    'observations.py': 'a9f951d4c12df99d0d78bf6eca3fdeee55539eb1bd3938e6e4fd71ae027b5210',
    'test_boundary_regression.py': '568b91f52eb49355d8a294eea219d3ca8a9d3970f248fb38cedc643bd5258da2',
    'test_observations.py': '545856f6d8c809ff9428186915c59034bb925ea6131d1427c68a047b7ff23611',
    'independent_checks.py': '315c792208e0fa64ba5223f6950792c9a94484602451f2f653079d1b4e1aa981',
    'example.py': '7c3121f8dd36b54fffbcb0ea00f6e9828a422feaeaa48dc184402bc332d0a224',
}
RELEASE_TOOLS = {'verify_release.py', 'seal_release.py', 'build_pdf.py',
                 'archive_release.py', 'archive_regression.py', 'tamper_regression.py'}
CHECKS = [
    {'label':'author', 'entry':'unittest', 'modules':['test_boundary_regression','test_observations'], 'tests':16},
    {'label':'independent', 'entry':'independent_checks.py', 'modules':[], 'tests':7},
    {'label':'example', 'entry':'example.py', 'modules':[], 'tests':None},
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


def stable_log(raw, count):
    text = raw.decode('utf-8')
    pattern = r'(?m)^Ran '+str(count)+r' tests in [0-9]+(?:\.[0-9]+)?s$'
    need(len(re.findall(pattern, text)) == 1, 'Replay: missing/ambiguous expected unittest count')
    need(text.endswith('\nOK\n'), 'Replay: missing exact unittest success suffix')
    return re.sub(pattern, 'Ran '+str(count)+' tests in <elapsed>s', text)


def verify_approval(root):
    review = read_json(root/'verification/release-review.json')
    need(type(review) is dict, 'Identity gate: release approval shape')
    need(review.get('schema') == 'report38-release-review-v1' and review.get('status') == 'APPROVED', 'Identity gate: final release is not approved')
    need(review.get('source_manifest_sha256') == SOURCE_MANIFEST_PIN and review.get('proof_sha256') == PROOF_PIN, 'Identity gate: release approval source mismatch')
    need(review.get('source_replay_status') == 'PASS', 'Identity gate: source replay not approved')
    for suffix in ('tex','pdf'):
        need(review.get('article_'+suffix+'_sha256') == sha((root/('Research_Report38.'+suffix)).read_bytes()), 'Identity gate: final article approval identity mismatch: '+suffix)


def verify_source(root):
    source = root/'evidence/source-packet'
    raw = (source/'manifest-sha256.json').read_bytes()
    need(sha(raw) == SOURCE_MANIFEST_PIN, 'Identity gate: frozen source manifest pin mismatch')
    manifest = parse_json(raw, 'Identity gate: source manifest')
    need(type(manifest) is dict and len(manifest) == 30, 'Identity gate: source manifest count/shape')
    for name, digest in manifest.items():
        safe_relative(name)
        need(name != 'manifest-sha256.json' and type(digest) is str and re.fullmatch('[0-9a-f]{64}', digest) is not None, 'Identity gate: source entry shape')
        need(sha((source/name).read_bytes()) == digest, 'Identity gate: frozen source bytes changed: '+name)
    names = set(manifest)|{'manifest-sha256.json'}
    actual = {p.relative_to(source).as_posix() for p in source.rglob('*') if p.is_file()}
    need(actual == names, 'Identity gate: source is not the exact frozen 31-file packet')
    need(sha((source/'PROOF.md').read_bytes()) == PROOF_PIN, 'Identity gate: frozen proof pin mismatch')
    for name,digest in ACTIVE_PROGRAMS.items():
        need(manifest[name] == digest, 'Identity gate: approved executable pin mismatch: '+name)
        need(not any(isinstance(n, ast.Assert) for n in ast.walk(ast.parse((source/name).read_bytes()))), 'Identity gate: removable assertion: '+name)
    expected_lineage = {'schema':'report38-source-lineage-v1','source_manifest_sha256':SOURCE_MANIFEST_PIN,'files':[]}
    for name in sorted(names):
        digest = sha((source/name).read_bytes())
        role = 'active pinned library or replay program' if name in ACTIVE_PROGRAMS else 'inert original source evidence'
        expected_lineage['files'].append({'packet':'one-visit-turmite-observations-20261003','original_relative_path':name,'packaged_relative_path':SOURCE_PREFIX+name,'original_sha256':digest,'packaged_sha256':digest,'normalization':'none; byte-exact','role':role})
    typed_equal(read_json(root/'verification/source-lineage.json'), expected_lineage, 'Identity gate: exact source lineage')
    expected = read_json(root/'verification/expected-receipts.json')
    need(type(expected) is dict and set(expected) == {'author','independent','example'}, 'Identity gate: expected receipt inventory')
    for check in CHECKS:
        label = check['label']
        if label == 'example':
            typed_equal(expected[label], read_json(source/'example-result.json'), 'Identity gate: expected example')
        else:
            for mode in ('normal','optimized'):
                typed_equal(expected[label], stable_log((source/(label+'-'+mode+'.log')).read_bytes(),check['tests']), 'Identity gate: frozen '+label+' '+mode+' stable log')
    typed_equal(read_json(root/'verification/replay-plan.json'), {'schema':'report38-replay-plan-v1','runtime':'Python 3.10+ standard library only','active_programs':ACTIVE_PROGRAMS,'checks':CHECKS,'inert_paths':['evidence/source-packet/boundary-context/','evidence/source-packet/verify_release.py'],'normalization':'only the elapsed time in exactly one unittest summary line'}, 'Identity gate: exact replay plan')
    return names


def verify_identity(root=ROOT):
    need(MANIFEST_SHA256 != '0'*64, 'Identity gate: release is not sealed')
    before = snapshot(root)
    raw = (root/'MANIFEST.json').read_bytes()
    need(sha(raw) == MANIFEST_SHA256, 'Identity gate: enclosing manifest digest mismatch')
    doc = parse_json(raw, 'Identity gate: manifest')
    need(type(doc) is dict and set(doc) == {'schema','release_stage','files','file_count','hash_convention'}, 'Identity gate: manifest shape')
    need(doc['schema'] == 'report38-release-inventory-v1', 'Identity gate: manifest schema')
    need(doc['release_stage'] in ('engineering-preview','final'), 'Identity gate: release stage')
    need(doc['hash_convention'] == HASH_CONVENTION, 'Identity gate: hash convention')
    files = doc['files']
    need(type(files) is dict and type(doc['file_count']) is int and doc['file_count'] == len(files), 'Identity gate: file count type/value')
    need(RELEASE_TOOLS <= set(files), 'Identity gate: missing release executable')
    dirs = {'.'}
    for name, record in files.items():
        rel = safe_relative(name)
        need(name not in ('MANIFEST.json','SHA256SUMS'), 'Identity gate: recursive inventory entry')
        need(type(record) is dict and set(record) == {'bytes','sha256','mode'}, 'Identity gate: entry shape')
        need(type(record['bytes']) is int and record['bytes'] >= 0, 'Identity gate: byte size type/value')
        need(type(record['mode']) is int and record['mode'] in (0o644,0o755), 'Identity gate: file mode type/value')
        need(type(record['sha256']) is str and re.fullmatch('[0-9a-f]{64}',record['sha256']) is not None, 'Identity gate: digest type/value')
        dirs.update(p.as_posix() for p in rel.parents)
    actual_files = {n for n,v in before.items() if v[0] is not None}
    actual_dirs = set(before)-actual_files
    need(actual_files == set(files)|{'MANIFEST.json','SHA256SUMS'} and actual_dirs == dirs, 'Identity gate: exact path inventory mismatch')
    for name, record in files.items():
        raw = (root/name).read_bytes()
        canonical = normalized_verifier(raw) if name == 'verify_release.py' else raw
        need(len(raw) == record['bytes'] and sha(canonical) == record['sha256'], 'Identity gate: payload digest mismatch: '+name)
        need(before[name][1] == record['mode'], 'Identity gate: payload mode mismatch: '+name)
    need(all(before[n][1] == 0o755 for n in actual_dirs), 'Identity gate: directory mode mismatch')
    need(before['MANIFEST.json'][1] == 0o644 and before['SHA256SUMS'][1] == 0o644, 'Identity gate: inventory mode mismatch')
    sums = ''.join(sha((root/n).read_bytes())+'  '+n+'\n' for n in sorted(set(files)|{'MANIFEST.json'}))
    need((root/'SHA256SUMS').read_text(encoding='utf-8') == sums, 'Identity gate: checksum inventory mismatch')
    for name in files:
        p = root/name
        if not name.startswith(SOURCE_PREFIX):
            if p.suffix == '.py':
                need(name in RELEASE_TOOLS, 'Identity gate: unexpected enclosing executable: '+name)
                need(not any(isinstance(n, ast.Assert) for n in ast.walk(ast.parse(p.read_bytes()))), 'Identity gate: removable assertion: '+name)
            if p.suffix in ('.py','.json','.md','.tex','.sh','.txt'):
                for prefix in (b'/' + b'workspace/', b'/' + b'home/', b'/' + b'root/'):
                    need(prefix not in p.read_bytes(), 'Identity gate: private absolute path: '+name)
        if p.suffix == '.json':read_json(p)
    source_names = verify_source(root)
    need({name for name in files if name.startswith('evidence/')} == {SOURCE_PREFIX+n for n in source_names}, 'Identity gate: unexpected evidence member')
    if doc['release_stage'] == 'final':
        need({'Research_Report38.tex','Research_Report38.pdf'} <= set(files), 'Identity gate: final article missing')
        verify_approval(root)
    return doc,before


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


def external_parent(value=None):
    # Resolve before mkdir or tempfile probing, so a hostile TMPDIR cannot cause
    # a write inside the release merely by selecting a temporary directory.
    candidates = [value] if value is not None else [os.environ[k] for k in ('TMPDIR','TEMP','TMP') if os.environ.get(k)] + ['/tmp','/var/tmp']
    for value in candidates:
        candidate = Path(value).resolve()
        need(candidate != ROOT and ROOT not in candidate.parents, 'Replay directory must be outside the release')
        if value is not None and len(candidates) == 1:
            candidate.mkdir(parents=True,exist_ok=True)
        if candidate.is_dir() and os.access(candidate,os.W_OK|os.X_OK):return candidate
    raise RuntimeError('No writable external temporary parent is available')


def full_replay(work_parent=None):
    manifest,before = verify_identity()
    expected = read_json(ROOT/'verification/expected-receipts.json')
    parent = external_parent(work_parent)
    env = {k:v for k,v in os.environ.items() if not k.startswith('PYTHON')}
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    modes = {}
    for mode,optimized in [('normal',False),('optimized',True)]:
        with tempfile.TemporaryDirectory(prefix='report38-'+mode+'-',dir=parent) as tmp:
            work = Path(tmp)/'relocated-release'
            shutil.copytree(ROOT,work,copy_function=shutil.copy2)
            _,copied_before = verify_identity(work)
            active = Path(tmp)/'active-programs';active.mkdir()
            for name,digest in ACTIVE_PROGRAMS.items():
                raw = (work/SOURCE_PREFIX/name).read_bytes()
                need(sha(raw) == digest, 'Replay executable is not approved: '+name)
                shutil.copy2(work/SOURCE_PREFIX/name,active/name)
            active_before = snapshot(active)
            records = {}
            for check in CHECKS:
                # -I excludes cwd, user packages and PYTHONPATH; only these six
                # hash-pinned files are added to the interpreter import path.
                # Neither the source verifier nor boundary-context is staged.
                runner = 'import runpy,sys; sys.path.insert(0,sys.argv[1]); '
                if check['label'] == 'author':
                    runner += "sys.argv=['unittest','-v','test_boundary_regression','test_observations']; runpy.run_module('unittest',run_name='__main__')"
                else:
                    need(check['entry'] in ACTIVE_PROGRAMS, 'Replay entry is not allowlisted')
                    runner += "p=sys.argv[1]+'/'+sys.argv[2]; sys.argv=[p]; runpy.run_path(p,run_name='__main__')"
                cmd = [sys.executable,'-I','-B']+(['-O'] if optimized else [])+['-c',runner,str(active),check['entry']]
                result = subprocess.run(cmd,cwd=Path(tmp),env=env,capture_output=True,timeout=1800)
                label = check['label']
                need(result.returncode == 0, 'Replay failed: '+label+': '+result.stderr[-3000:].decode('utf-8','replace'))
                if label == 'example':
                    need(result.stderr == b'', 'Unexpected example stderr')
                    typed_equal(parse_json(result.stdout,'example '+mode),expected[label],'example '+mode)
                    need(result.stdout == (ROOT/SOURCE_PREFIX/'example-result.json').read_bytes(), 'Example receipt byte inequality')
                    stable = result.stdout
                else:
                    stable = stable_log(result.stdout+result.stderr,check['tests']).encode('utf-8')
                    typed_equal(stable.decode('utf-8'),expected[label],label+' '+mode+' stable log')
                records[label] = {'status':'PASS','exit_code':result.returncode,'test_count':check['tests'],'stable_output_sha256':sha(stable),'stable_output_bytes':len(stable)}
                need(snapshot(active) == active_before, 'Active replay source bytes/modes/mtimes changed')
                need(snapshot(work) == copied_before, 'Copied release bytes/modes/mtimes changed')
                verify_identity(work)
            modes[mode] = records
    typed_equal(modes['normal'],modes['optimized'],'normal/optimized stable replay')
    regression = semantic_regression()
    need(snapshot(ROOT) == before, 'Original release bytes/modes/mtimes changed during replay')
    verify_identity()
    return {'schema':'report38-replay-v1','status':'PASS','manifest_sha256':MANIFEST_SHA256,'release_stage':manifest['release_stage'],'identity_verified_before_copied_execution':True,'fresh_external_copies':2,'normal_optimized_stable_outputs_equal':True,'only_excluded_field':'unittest summary elapsed time','original_and_copied_bytes_modes_mtimes_preserved':True,'boundary_context_executed':False,'source_packet_verifier_executed':False,'active_programs':sorted(ACTIVE_PROGRAMS),'strict_receipt_regression':regression,'modes':modes,'scope':'Finite exact corroboration of the one-visit boundary and observation queries; not proof by testing or a claim beyond the proved boundary.'}


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
        result = {'schema':'report38-identity-v1','status':'PASS','manifest_sha256':MANIFEST_SHA256,'release_stage':doc['release_stage'],'file_count':doc['file_count']}
    else:result = full_replay(args.workdir)
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__ == '__main__':
    try:main()
    except (RuntimeError,OSError,ValueError,SyntaxError,RecursionError,subprocess.SubprocessError) as exc:
        print(str(exc),file=sys.stderr)
        raise SystemExit(1)
