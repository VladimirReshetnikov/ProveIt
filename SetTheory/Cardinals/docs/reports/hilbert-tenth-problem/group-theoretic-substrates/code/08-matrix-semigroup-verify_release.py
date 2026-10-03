#!/usr/bin/env python3
"""Identity-gated, strict-JSON replay of the Report32 release. Standard library only."""
import argparse
import ast
import copy
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import subprocess
import sys
import tempfile

MANIFEST_SHA256 = "a9ef2e1b00d0d3627879719791d5ad121ccc21b17c17ca8de6dc34808b01a7f3"
ROOT = Path(__file__).resolve().parent
SEMIGROUP_PIN = '506144b361b2bea634d468a94921644d91868dc089a257fe289a0bf51b74cec9'
WITNESS_PIN = '13a3857d28b0207d9baa83facac5b2e67bbaeb858d00b82ef9a91c4ab38df890'
TABLE_PIN = '0c6d8ae506f503e2783f6ed2ee68db4cde2f501b9864f376ab3773f86b59428a'
PIN_PATTERN = rb'(?m)^MANIFEST_SHA256 = "[0-9a-f]{64}"$'
ZERO_PIN_LINE = b'MANIFEST_SHA256 = "' + b'0'*64 + b'"'


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def normalized_verifier(raw):
    require(len(re.findall(PIN_PATTERN, raw)) == 1, 'Verifier self-pin format mismatch')
    return re.sub(PIN_PATTERN, ZERO_PIN_LINE, raw)


def parse_json(raw, label='JSON'):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, label + ': duplicate key ' + key)
            result[key] = value
        return result
    def invalid_constant(value):
        raise RuntimeError(label + ': nonfinite JSON number ' + value)
    try:
        return json.loads(raw, object_pairs_hook=pairs, parse_constant=invalid_constant)
    except (ValueError, UnicodeDecodeError) as exc:
        raise RuntimeError(label + ': invalid JSON') from exc


def read_json(path):
    return parse_json(path.read_bytes(), path.name)


def typed_equal(actual, expected, label='receipt'):
    require(type(actual) is type(expected), label + ': exact JSON type mismatch')
    if type(expected) is dict:
        require(set(actual) == set(expected), label + ': exact key set mismatch')
        for key in expected:
            typed_equal(actual[key], expected[key], label + '.' + key)
    elif type(expected) is list:
        require(len(actual) == len(expected), label + ': exact list length mismatch')
        for index, (a, b) in enumerate(zip(actual, expected)):
            typed_equal(a, b, label + '[' + str(index) + ']')
    else:
        require(actual == expected, label + ': expected value mismatch')


def safe_relative(name):
    require(type(name) is str and bool(re.fullmatch(r'[A-Za-z0-9_./-]+', name)), 'Unsafe inventory path')
    path = PurePosixPath(name)
    require(not path.is_absolute() and all(p not in ('', '.', '..') for p in name.split('/')), 'Unsafe inventory path')
    require(path.as_posix() == name, 'Noncanonical inventory path')
    return path


def snapshot(root):
    result = {}
    for path in sorted(root.rglob('*')):
        rel = path.relative_to(root).as_posix()
        require(not path.is_symlink(), 'Identity gate: symlink mismatch: ' + rel)
        mode = path.stat().st_mode
        require(stat.S_ISREG(mode) or stat.S_ISDIR(mode), 'Identity gate: special path mismatch: ' + rel)
        result[rel] = (sha(path.read_bytes()) if path.is_file() else None,
                       stat.S_IMODE(mode), path.stat().st_mtime_ns)
    return result


def verify_identity(root=ROOT):
    require(MANIFEST_SHA256 != '0'*64, 'Identity gate: release is unsealed')
    # No copied/imported payload code has been loaded at this point.
    state = snapshot(root)
    require('MANIFEST.json' in state and 'SHA256SUMS' in state, 'Identity gate: missing inventory')
    raw = (root/'MANIFEST.json').read_bytes()
    require(sha(raw) == MANIFEST_SHA256, 'Identity gate: manifest digest mismatch')
    manifest = parse_json(raw, 'manifest')
    require(type(manifest) is dict and set(manifest) == {'schema','release_stage','files','file_count','hash_convention'}, 'Identity gate: manifest schema mismatch')
    require(manifest['schema'] == 'report32-release-inventory-v1', 'Identity gate: manifest version mismatch')
    require(type(manifest['release_stage']) is str and manifest['release_stage'] in ('engineering-preview','final'), 'Identity gate: release stage mismatch')
    require(manifest['hash_convention'] == 'sha256; verify_release.py self-pin line normalized to 64 zeros; all other files byte-exact', 'Identity gate: hash convention mismatch')
    entries = manifest['files']
    require(type(entries) is dict and type(manifest['file_count']) is int and manifest['file_count'] == len(entries), 'Identity gate: file count type/value mismatch')
    require('verify_release.py' in entries, 'Identity gate: verifier missing from inventory')
    expected_dirs = set()
    for name, record in entries.items():
        path = safe_relative(name)
        require(name not in ('MANIFEST.json','SHA256SUMS'), 'Identity gate: recursive inventory entry')
        require(type(record) is dict and set(record) == {'bytes','sha256'}, 'Identity gate: entry schema mismatch')
        require(type(record['bytes']) is int and record['bytes'] >= 0, 'Identity gate: size type mismatch')
        require(type(record['sha256']) is str and re.fullmatch('[0-9a-f]{64}', record['sha256']) is not None, 'Identity gate: hash type mismatch')
        for parent in path.parents:
            if parent.as_posix() != '.':
                expected_dirs.add(parent.as_posix())
    expected_files = set(entries) | {'MANIFEST.json','SHA256SUMS'}
    actual_files = {n for n, v in state.items() if v[0] is not None}
    actual_dirs = set(state) - actual_files
    require(actual_files == expected_files and actual_dirs == expected_dirs, 'Identity gate: exact required path set mismatch')
    if manifest['release_stage'] == 'final':
        require({'report32.tex','report32.pdf'} <= set(entries), 'Identity gate: final report missing')
    for name, record in entries.items():
        raw = (root/name).read_bytes()
        canonical = normalized_verifier(raw) if name == 'verify_release.py' else raw
        require(len(raw) == record['bytes'] and sha(canonical) == record['sha256'], 'Identity gate: payload digest mismatch: ' + name)
    wanted_sums = ''.join(sha((root/name).read_bytes())+'  '+name+'\n' for name in sorted(set(entries)|{'MANIFEST.json'}))
    require((root/'SHA256SUMS').read_text(encoding='utf-8') == wanted_sums, 'Identity gate: exact checksum inventory mismatch')
    for name in entries:
        path = root/name
        if path.suffix == '.py':
            require(not any(isinstance(node, ast.Assert) for node in ast.walk(ast.parse(path.read_bytes()))), 'Python assertion statement is forbidden: ' + name)
        if path.suffix in {'.py','.json','.md','.tex','.sh','.txt','.log'}:
            raw = path.read_bytes()
            for prefix in (b'/' + b'workspace/', b'/' + b'home/', b'/' + b'root/', b'/' + b'tmp/'):
                require(prefix not in raw, 'Private absolute path found: ' + name)
    for name, pin in [('core/data/semigroup.json',SEMIGROUP_PIN),('paired/data/semigroup.json',SEMIGROUP_PIN),('core/evidence/accepting-witness.json',WITNESS_PIN),('paired/data/accepting-witness.json',WITNESS_PIN),('core/data/u15_table.json',TABLE_PIN),('fiber/data/semigroup.json',SEMIGROUP_PIN),('fiber/data/accepting-witness.json',WITNESS_PIN)]:
        require(sha((root/name).read_bytes()) == pin, 'Shared scientific data pin mismatch: ' + name)
    expected = read_json(root/'verification/expected-receipts.json')
    require(type(expected) is dict and len(expected) == 19, 'Expected receipt inventory mismatch')
    for name, receipt in expected.items():
        safe_relative(name)
        require(name in entries, 'Expected receipt is not identity checked')
        typed_equal(read_json(root/name), receipt, 'stored ' + name)
    return manifest, state


def semantic_regression():
    cases = [(True,1),(False,0),(1,True),(1.0,1),({'count':True},{'count':1}),
             ({'sos':False},{'sos':0}),([False],[0]),({'n':1,'extra':0},{'n':1}),
             ({},{'n':1}),([1],[1,2]),(None,0),('1',1)]
    for a, b in cases:
        try:
            typed_equal(a,b)
        except RuntimeError:
            pass
        else:
            raise RuntimeError('Strict receipt regression accepted malformed value')
    rejected_json = ['{"x":1,"x":1}', '{"n":NaN}', '{"n":Infinity}']
    for raw in rejected_json:
        try:
            parse_json(raw)
        except RuntimeError:
            pass
        else:
            raise RuntimeError('Strict parser accepted invalid JSON')
    typed_equal({'ok':True,'count':1,'zero':0,'x':[None,'a']}, {'ok':True,'count':1,'zero':0,'x':[None,'a']})
    return {'status':'PASS','typed_mutations_rejected':len(cases),'invalid_json_rejected':len(rejected_json)}


def run_script(root, relative, optimized, args=()):
    # -I removes ambient Python import paths and user site; imported sibling code
    # is located explicitly by the identity-checked source scripts.
    command = [sys.executable,'-I','-B'] + (['-O'] if optimized else []) + [str(root/relative)] + list(args)
    env = dict(os.environ)
    for key in list(env):
        if key.startswith('PYTHON'):
            del env[key]
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    done = subprocess.run(command,cwd=root/relative.split('/')[0],env=env,capture_output=True,text=True,timeout=900)
    require(done.returncode == 0, 'Replay command failed: ' + relative + ': ' + done.stderr[-2000:])
    require(not done.stderr.strip(), 'Unexpected replay stderr: ' + relative)
    return done.stdout


def full_replay():
    manifest, before = verify_identity()
    expected = read_json(ROOT/'verification/expected-receipts.json')
    modes = {}
    for mode, optimized in [('normal',False),('optimized',True)]:
        # A complete newly copied tree is reverified before any copied program runs.
        with tempfile.TemporaryDirectory(prefix='report32-'+mode+'-') as tmp:
            work = Path(tmp)/'relocated-release'
            shutil.copytree(ROOT,work,copy_function=shutil.copy2)
            verify_identity(work)
            records = {}
            def checked(label, script, expected_path, args=()):
                receipt = parse_json(run_script(work,script,optimized,args), label)
                typed_equal(receipt, expected[expected_path], label + ' ' + mode)
                records[label] = receipt
                return receipt
            checked('core_build','core/compiler.py','core/data/ledger.json',('build',))
            for name in ('semigroup.json','ledger.json','matrices.txt'):
                require((work/'core/data'/name).read_bytes() == (ROOT/'core/data'/name).read_bytes(), 'Core rebuild byte inequality: ' + name)
            checked('core_authored','core/tests/check_all.py','core/evidence/tests'+('-optimized' if optimized else '')+'.json')
            require((work/'core/evidence/accepting-witness.json').read_bytes() == (ROOT/'core/evidence/accepting-witness.json').read_bytes(),'Rebuilt witness byte inequality')
            checked('core_json_only','core/audit/independent_check.py','core/audit/independent-results.json')
            checked('paired_authored','paired/tests/check_all.py','paired/evidence/tests'+('-optimized' if optimized else '')+'.json')
            for name in ('accepting-94-certificate.json','accepting-94-ledger.json'):
                require((work/'paired/examples'/name).read_bytes() == (ROOT/'paired/examples'/name).read_bytes(), 'Paired rebuild byte inequality: ' + name)
            checked('paired_json_only','paired/audit/source_literal_check.py','paired/audit/source_literal_check.json')
            checked('paired_interface','paired/audit/independent_interface_check.py','paired/audit/independent_interface_check.json')
            checked('literal_polynomial_json_only','verification/audit_literal_polynomials.py','verification/literal-polynomials.json')
            checked('accepting_certificate','paired/paired_compiler.py','paired/evidence/accepting-cli-check.json',('verify','examples/accepting-94-certificate.json'))
            export_count = 0
            for r in range(3):
                for domain in ('signed','natural'):
                    stdout = run_script(work,'paired/paired_compiler.py',optimized,('export',str(r),'--mode',domain))
                    saved = ROOT/'paired/examples'/('r'+str(r)+'-'+domain+'-sos.json')
                    typed_equal(parse_json(stdout),read_json(saved),'literal export')
                    require(stdout.encode() == saved.read_bytes(),'Literal polynomial export byte inequality')
                    export_count += 1
            witness = read_json(ROOT/'core/evidence/accepting-witness.json')
            args = ('certificate',json.dumps(witness['inner_tile_sequence'],separators=(',',':')))
            stdout = run_script(work,'paired/paired_compiler.py',optimized,args)
            require(stdout.encode() == (ROOT/'paired/examples/accepting-94-certificate.json').read_bytes(),'CLI accepting certificate byte inequality')
            r0 = run_script(work,'paired/paired_compiler.py',optimized,('certificate','[]','--mode','natural'))
            (work/'paired/r0-natural-certificate.json').write_text(r0)
            checked('r0_natural_certificate','paired/paired_compiler.py','paired/audit/cli_r0_natural_check.json',('verify','r0-natural-certificate.json'))
            checked('fiber_authored_json_only','fiber/check_fibers.py','fiber/normal-run.json')
            require((work/'fiber/CHECKS.json').read_bytes() == (ROOT/'fiber/CHECKS.json').read_bytes(),'Fiber receipt rebuild byte inequality')
            checked('fiber_independent_json_only','fiber/audit/independent_check.py','fiber/audit/normal.json')
            records['literal_exports_rebuilt'] = export_count
            modes[mode] = records
    # The two explicit optimization-mode booleans legitimately differ.
    a,b = copy.deepcopy(modes['normal']),copy.deepcopy(modes['optimized'])
    for label,key in [('core_authored','optimization_mode'),('paired_authored','optimized_python')]:
        typed_equal(a[label][key],False,label+' normal mode')
        typed_equal(b[label][key],True,label+' optimized mode')
        del a[label][key];del b[label][key]
    typed_equal(a,b,'normal/-O semantic receipt equality')
    regression = semantic_regression()
    require(snapshot(ROOT) == before,'Original release bytes/modes/mtimes changed during replay')
    verify_identity()
    return {'schema':'report32-replay-v1','status':'PASS','release_stage':manifest['release_stage'],
            'manifest_sha256':MANIFEST_SHA256,'identity_verified_before_copied_execution':True,
            'fresh_isolated_copies':2,'normal_optimized_semantics_equal':True,
            'original_bytes_modes_mtimes_preserved':True,'strict_receipt_regression':regression,
            'compiler_rebuild_byte_equality':True,'common_data_and_witness_pins_verified':True,
            'modes':modes,'scope':'Finite replay of the sealed artifacts; universal claims and fixed-r scope require the accompanying proofs.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--verify-only',action='store_true')
    group.add_argument('--self-test-types',action='store_true')
    group.add_argument('--replay',action='store_true')
    args = parser.parse_args()
    manifest, _ = verify_identity()
    if args.verify_only:
        result = {'status':'PASS','release_stage':manifest['release_stage'],'manifest_sha256':MANIFEST_SHA256,
                  'payload_files':manifest['file_count'],'copied_code_executed':False}
    elif args.self_test_types:
        result = semantic_regression()
    else:
        result = full_replay()
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__ == '__main__':
    main()
