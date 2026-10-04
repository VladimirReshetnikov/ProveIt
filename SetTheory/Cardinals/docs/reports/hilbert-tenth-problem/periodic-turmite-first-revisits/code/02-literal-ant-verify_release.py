#!/usr/bin/env python3
"""Identity-gated Report40 replay of literal ant, endpoint and companion packets.

Authenticate the complete release archive with a trusted external hash tool
before running any packaged program. A self-reported PASS is not a trust anchor.
Only pinned own-code in mutable external copies executes. Historical changed-file
originals remain inert. Literal scientific replay is unoptimized only.
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

MANIFEST_SHA256 = "f44d98ff3184e3c2ceeaaa8c0da40688056902338ee39d3f534091d5be9df5bd"
ROOT = Path(__file__).resolve().parent
PIN_PATTERN = rb'(?m)^MANIFEST_SHA256 = "[0-9a-f]{64}"$'
ZERO_PIN_LINE = b'MANIFEST_SHA256 = "' + b'0'*64 + b'"'
HASH_CONVENTION = 'sha256; verify_release.py self-pin line normalized to 64 zeros; all other files byte-exact'
SOURCE_MANIFEST_PIN = 'e31de0a0a06b917c60071d500b72dd7891cd74bea103e449685c0041c9b0f615'
ORIGINAL_MANIFEST_PIN = 'a82fdb40349bdb3be08b7454f706232c0a7ac9d855484336abc8bb87497fcd0a'
ENDPOINT_MANIFEST_PIN = '31fb4d8feedae85446fdf6cf480ec1e5ed6a2ffd3ccb16cb15887503093e5112'
COMPANION_MANIFEST_PIN = '115cf44fb4f42f346fdb45319b13edbda0dc5251aac02cc17e541ba0df77d79c'
PROOF_PIN = 'a8b4a65ad97a06f3c854a9d133e67dca240d6212749f42ed6c4a92b30318483b'
SOURCE_PREFIX = 'evidence/'
RELEASE_TOOLS = {'verify_release.py','seal_release.py','build_pdf.py','archive_release.py','archive_regression.py','tamper_regression.py'}
LITERAL = 'evidence/literal-interface'
ENDPOINT = 'evidence/endpoint'
COMPANION = 'evidence/one-visit-companion'
AUDIT = 'evidence/independent-audit'
ENDPOINT_AUDIT = 'evidence/endpoint-independent-audit'


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
    need(review.get('schema') == 'report40-release-review-v1' and review.get('status') == 'APPROVED', 'Identity gate: final release is not approved')
    need(review.get('source_manifest_sha256') == SOURCE_MANIFEST_PIN and review.get('proof_sha256') == PROOF_PIN, 'Identity gate: release approval source mismatch')
    need(review.get('source_replay_status') == 'PASS', 'Identity gate: source replay not approved')
    need(review.get('endpoint_manifest_sha256') == ENDPOINT_MANIFEST_PIN and review.get('endpoint_independent_audit_status') == 'PASS', 'Identity gate: endpoint approval missing')
    need(review.get('article_review_status') == 'PASS' and review.get('visual_qa_status') == 'PASS', 'Identity gate: article review not approved')
    typed_equal(review.get('article_auxiliary_sha256'),{p.relative_to(root).as_posix():sha(p.read_bytes()) for p in sorted((root/'figures').glob('*.tex'))},'Identity gate: article auxiliary approval')
    for suffix in ('tex','pdf'):
        need(review.get('article_'+suffix+'_sha256') == sha((root/('Research_Report40.'+suffix)).read_bytes()), 'Identity gate: final article approval identity mismatch: '+suffix)


def listed_packet(root, prefix, pin, count):
    base=root/prefix
    raw=(base/'MANIFEST.json').read_bytes()
    need(sha(raw)==pin,'Identity gate: source manifest pin mismatch: '+prefix)
    doc=parse_json(raw,'source manifest')
    need(type(doc) is dict and type(doc.get('files')) is list and len(doc['files'])==count,'Identity gate: source manifest shape')
    entries={}
    for record in doc['files']:
        need(type(record) is dict and set(record)=={'path','bytes','sha256'},'Identity gate: source record shape')
        name=record['path'];safe_relative(name)
        need(name not in entries and name!='MANIFEST.json','Identity gate: duplicate source name')
        need(type(record['bytes']) is int and record['bytes']>=0 and type(record['sha256']) is str,'Identity gate: source scalar type')
        raw=(base/name).read_bytes()
        need(len(raw)==record['bytes'] and sha(raw)==record['sha256'],'Identity gate: source bytes mismatch: '+name)
        entries[name]=record['sha256']
    actual={p.relative_to(base).as_posix() for p in base.rglob('*') if p.is_file()}
    need(actual==set(entries)|{'MANIFEST.json'},'Identity gate: source exact inventory mismatch: '+prefix)
    return entries


def verify_source(root):
    active=listed_packet(root,LITERAL,SOURCE_MANIFEST_PIN,92)
    endpoint=listed_packet(root,ENDPOINT,ENDPOINT_MANIFEST_PIN,23)
    need(sha((root/LITERAL/'atlas/PROOF.md').read_bytes())==PROOF_PIN,'Identity gate: global proof pin')
    predecessor=root/'evidence/predecessor'
    raw=(predecessor/'MANIFEST.json').read_bytes()
    need(sha(raw)==ORIGINAL_MANIFEST_PIN,'Identity gate: original manifest pin')
    old=parse_json(raw)['files'];oldmap={x['path']:x for x in old}
    need(len(oldmap)==len(old)==92 and set(oldmap)==set(active),'Identity gate: predecessor inventory')
    changed=[];rows=[]
    for name in sorted(set(active)|{'MANIFEST.json'}):
        safe_relative(name)
        current=root/LITERAL/name
        oldpath=predecessor/name if (predecessor/name).is_file() else current
        raw=oldpath.read_bytes();different=raw!=current.read_bytes()
        if name!='MANIFEST.json':
            need(len(raw)==oldmap[name]['bytes'] and sha(raw)==oldmap[name]['sha256'],'Identity gate: predecessor reconstruction mismatch')
        if different:changed.append(name)
        rows.append({'path':name,'original_sha256':sha(raw),'active_sha256':sha(current.read_bytes()),'predecessor_location':oldpath.relative_to(root).as_posix(),'active_location':current.relative_to(root).as_posix(),'changed':different})
    need(set(p.relative_to(predecessor).as_posix() for p in predecessor.rglob('*') if p.is_file())==set(changed),'Identity gate: predecessor exact difference inventory')
    lineage={'schema':'report40-source-lineage-v1','original_manifest_sha256':ORIGINAL_MANIFEST_PIN,'active_manifest_sha256':SOURCE_MANIFEST_PIN,'original_zip_sha256':'41081f538ca24e527cbf295626760f3339ed9dd9d171e725fb35131166d6a650','active_zip_sha256':'70a2a87ddb1ab018ec8c795dad56d053f66855a9b47ab7f3a9b64cf1164b852f','source_files':rows,'changed_paths':changed,'canonical_active_zip_files':93,'source_root_caches_packaged':False,'originals_reconstructible_from_recorded_locations':True}
    typed_equal(read_json(root/'verification/source-lineage.json'),lineage,'Identity gate: source lineage')
    need(sha((root/COMPANION/'MANIFEST.json').read_bytes())==COMPANION_MANIFEST_PIN,'Identity gate: companion manifest pin')
    companion=read_json(root/COMPANION/'MANIFEST.json')
    need(type(companion) is dict and companion.get('release_stage')=='final','Identity gate: companion release stage')
    for name,entry in companion['files'].items():
        safe_relative(name);raw=(root/COMPANION/name).read_bytes()
        need(len(raw)==entry['bytes'] and sha(normalized_verifier(raw) if name=='verify_release.py' else raw)==entry['sha256'],'Identity gate: companion payload pin: '+name)
    expected=read_json(root/'verification/expected-receipts.json')
    typed_equal(expected,{'literal':read_json(root/LITERAL/'atlas/fresh_replay.json'),'endpoint':read_json(root/ENDPOINT/'fresh_replay.json'),'independent_interface':read_json(root/AUDIT/'independent_interface_checks.json'),'independent_endpoint':read_json(root/ENDPOINT_AUDIT/'independent_dag_check.json')},'Identity gate: expected receipts')
    plan={'schema':'report40-replay-plan-v1','literal_programs':{n:active[n] for n in sorted(active) if n.endswith('.py')},'literal_commands':[v['script'] for v in expected['literal']['commands']],'literal_outputs':[v['file'] for v in expected['literal']['byte_exact_outputs']],'endpoint_programs':{n:endpoint[n] for n in sorted(endpoint) if n.endswith('.py')},'endpoint_commands':[v['command'] for v in expected['endpoint']['commands']],'endpoint_outputs':[v['file'] for v in expected['endpoint']['byte_exact_outputs']],'independent_interface_program_sha256':sha((root/AUDIT/'independent_interface_checks.py').read_bytes()),'independent_endpoint_program_sha256':sha((root/ENDPOINT_AUDIT/'independent_dag_check.py').read_bytes()),'companion_entry':'verify_release.py --replay','scientific_execution':'literal, endpoint and additional audits unoptimized only; Report38 separately supports normal and optimized replay','frozen_roots_never_executed':True,'historical_predecessor_executed':False}
    typed_equal(read_json(root/'verification/replay-plan.json'),plan,'Identity gate: replay allowlist')
    need(len(plan['literal_programs'])==34 and len(plan['literal_commands'])==28 and len(plan['literal_outputs'])==39,'Identity gate: literal replay counts')
    need(len(plan['endpoint_commands'])==4 and len(plan['endpoint_outputs'])==10,'Identity gate: endpoint replay counts')
    audit=read_json(root/AUDIT/'replay_verification.json')
    need(audit['status']=='PASS_INDEPENDENT_HARDENED_PACKET_AUDIT' and audit['commands']==28 and audit['exact_scientific_outputs']==39,'Identity gate: independent literal approval')
    endpoint_audit=read_json(root/ENDPOINT_AUDIT/'external_qa_summary.json')
    need(endpoint_audit['status']=='PASS_EXTERNAL_ENDPOINT_QA' and endpoint_audit['normal_replay_commands']==4 and endpoint_audit['byte_exact_DAGs']==6 and endpoint_audit['byte_exact_receipts']==4,'Identity gate: independent endpoint approval')
    need(expected['independent_endpoint']['status']=='PASS_EXTERNAL_DATA_ONLY_DAG_CHECK','Identity gate: independent endpoint polynomial approval')
    return active


def verify_identity(root=ROOT):
    need(MANIFEST_SHA256 != '0'*64, 'Identity gate: release is not sealed')
    before = snapshot(root)
    raw = (root/'MANIFEST.json').read_bytes()
    need(sha(raw) == MANIFEST_SHA256, 'Identity gate: enclosing manifest digest mismatch')
    doc = parse_json(raw, 'Identity gate: manifest')
    need(type(doc) is dict and set(doc) == {'schema','release_stage','files','file_count','hash_convention'}, 'Identity gate: manifest shape')
    need(doc['schema'] == 'report40-release-inventory-v1', 'Identity gate: manifest schema')
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
    if doc['release_stage'] == 'final':
        need({'Research_Report40.tex','Research_Report40.pdf'} <= set(files), 'Identity gate: final article missing')
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


def execute(cmd,cwd,env,label,timeout=14400):
    done=subprocess.run(cmd,cwd=cwd,env=env,capture_output=True,timeout=timeout)
    need(done.returncode==0,'Replay failed: '+label+': '+done.stderr[-4000:].decode('utf-8','replace'))
    need(done.stderr==b'','Replay unexpected stderr: '+label)
    return done.stdout


def full_replay(work_parent=None):
    manifest,before=verify_identity()
    parent=external_parent(work_parent)
    expected=read_json(ROOT/'verification/expected-receipts.json')
    env={k:v for k,v in os.environ.items() if not k.startswith('PYTHON')}
    env['PYTHONDONTWRITEBYTECODE']='1'
    outcomes={}
    with tempfile.TemporaryDirectory(prefix='report40-replay-',dir=parent) as tmp:
        tmp=Path(tmp);env['TMPDIR']=str(tmp)
        for label,prefix,receipt in [('literal',LITERAL,'atlas/fresh_replay.json'),('endpoint',ENDPOINT,'fresh_replay.json')]:
            work=tmp/label;shutil.copytree(ROOT/prefix,work,copy_function=shutil.copy2)
            source_before=snapshot(work)
            raw=execute([sys.executable,'-I','-B',str(work/'replay_all.py')],Path('/'),env,label)
            typed_equal(read_json(work/receipt),expected[label],label+' exact receipt')
            need((work/receipt).read_bytes()==(ROOT/prefix/receipt).read_bytes(),label+' byte-exact receipt')
            after=snapshot(work)
            need(set(after)==set(source_before),'Mutable copied source path inventory changed')
            need(all(after[n][:2]==source_before[n][:2] for n in after),'Mutable copied source bytes/modes changed')
            # Driver rewrites its receipt, so copied-tree mtimes are intentionally not compared.
            outcomes[label]={'status':'PASS','commands':len(expected[label]['commands']),'byte_exact_outputs':len(expected[label]['byte_exact_outputs']),'receipt_sha256':sha((work/receipt).read_bytes()),'stdout_sha256':sha(raw),'copied_bytes_modes_preserved':True,'copied_mtimes_preservation_claimed':False}
        audit=tmp/'interface-audit';audit.mkdir();shutil.copytree(ROOT/LITERAL,audit/'extracted',copy_function=shutil.copy2)
        shutil.copy2(ROOT/AUDIT/'independent_interface_checks.py',audit/'independent_interface_checks.py')
        env['AUDIT_ROOT']=str(audit)
        raw=execute([sys.executable,'-I','-B',str(audit/'independent_interface_checks.py')],Path('/'),env,'independent interface')
        typed_equal(read_json(audit/'independent_interface_checks.json'),expected['independent_interface'],'independent interface receipt')
        need((audit/'independent_interface_checks.json').read_bytes()==(ROOT/AUDIT/'independent_interface_checks.json').read_bytes(),'Independent interface byte equality')
        outcomes['independent_interface']={'status':'PASS','valid_input_cases':85,'nested_mutable_containers_mutated':2838,'receipt_sha256':sha((audit/'independent_interface_checks.json').read_bytes())}
        ea=tmp/'endpoint-audit';ea.mkdir()
        er=ea/'authenticated_extraction'/'literal-turmite-endpoint-release-20261003'
        er.parent.mkdir();shutil.copytree(ROOT/ENDPOINT,er,copy_function=shutil.copy2)
        shutil.copy2(ROOT/ENDPOINT_AUDIT/'independent_dag_check.py',ea/'independent_dag_check.py')
        raw=execute([sys.executable,'-I','-B',str(ea/'independent_dag_check.py')],Path('/'),env,'independent endpoint')
        typed_equal(read_json(ea/'independent_dag_check.json'),expected['independent_endpoint'],'independent endpoint receipt')
        need((ea/'independent_dag_check.json').read_bytes()==(ROOT/ENDPOINT_AUDIT/'independent_dag_check.json').read_bytes(),'Independent endpoint byte equality')
        outcomes['independent_endpoint']={'status':'PASS','DAGs':6,'receipt_sha256':sha((ea/'independent_dag_check.json').read_bytes())}
        comp=tmp/'companion';shutil.copytree(ROOT/COMPANION,comp,copy_function=shutil.copy2)
        raw=execute([sys.executable,'-I','-B',str(comp/'verify_release.py'),'--replay'],Path('/'),env,'Report38 companion')
        out=parse_json(raw,'companion replay');need(out['status']=='PASS' and out['manifest_sha256']==COMPANION_MANIFEST_PIN,'Companion replay identity')
        outcomes['companion']={'status':'PASS','manifest_sha256':COMPANION_MANIFEST_PIN,'normal_optimized_stable_outputs_equal':out['normal_optimized_stable_outputs_equal'],'receipt_sha256':sha(raw)}
    regression=semantic_regression()
    need(snapshot(ROOT)==before,'Original release bytes/modes/mtimes changed during replay')
    verify_identity()
    return {'schema':'report40-replay-v1','status':'PASS','manifest_sha256':MANIFEST_SHA256,'release_stage':manifest['release_stage'],'identity_verified_before_copied_execution':True,'original_bytes_modes_mtimes_preserved':True,'literal_and_endpoint_science_unoptimized_only':True,'literal_explicit_optimization_refusals':27,'literal_unsupported_optimized_entries':2,'original_or_historical_source_executed':False,'strict_receipt_regression':regression,'outcomes':outcomes,'scope':'Finite exact corroboration and source identity, supporting the separately stated mathematical global proof; no dense-board expansion, published U15 compiler implementation, or combined universal arithmetic cost.'}


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
        result = {'schema':'report40-identity-v1','status':'PASS','manifest_sha256':MANIFEST_SHA256,'release_stage':doc['release_stage'],'file_count':doc['file_count']}
    else:result = full_replay(args.workdir)
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__ == '__main__':
    try:main()
    except (RuntimeError,OSError,ValueError,SyntaxError,RecursionError,subprocess.SubprocessError) as exc:
        print(str(exc),file=sys.stderr)
        raise SystemExit(1)
