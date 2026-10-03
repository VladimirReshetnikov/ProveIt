#!/usr/bin/env python3
"""Portable identity-gated replay, Python 3.9+ standard library only.

This launcher is the small trust root. Its manifest digest is frozen below.
Only checks.py is executable evidence, and its verified bytes are compiled only
AFTER every package hash passes. Upstream .py caches remain inert bytes.
"""
import argparse
import hashlib
import json
import pathlib
import subprocess
import sys
import tempfile

FROZEN_MANIFEST_SHA256 = '07ad20229a9ac95f4958ff4d2dea1cb9e32becf0f3f552128de84ae872ffaebf'
ROOT = pathlib.Path(__file__).resolve().parent

class ReplayFailure(Exception):
    pass

def need(condition, message):
    if condition is not True:
        raise ReplayFailure(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def object_unique(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'Duplicate JSON object key')
        result[key] = value
    return result

def bad_constant(value):
    raise ReplayFailure('Nonfinite JSON constant: ' + value)

def decode(data):
    return json.loads(data.decode('utf-8'), object_pairs_hook=object_unique,
                      parse_constant=bad_constant)

def identity_gate():
    raw = (ROOT/'FROZEN_HASHES.json').read_bytes()
    need(digest(raw) == FROZEN_MANIFEST_SHA256,
         'Identity gate failed: manifest SHA256 mismatch')
    manifest = decode(raw)
    need(type(manifest) is dict and set(manifest) == {'schema','files'},
         'Identity gate failed: manifest shape')
    need(manifest['schema'] == 'research-report33-supplement-frozen-v1' and
         type(manifest['files']) is dict, 'Identity gate failed: manifest schema')
    data = {}
    for name, expected in manifest['files'].items():
        rel = pathlib.PurePosixPath(name)
        need(type(name) is str and not rel.is_absolute() and '..' not in rel.parts
             and str(rel) == name and name not in ['verify.py','FROZEN_HASHES.json'],
             'Identity gate failed: unsafe manifest path')
        path = ROOT.joinpath(*rel.parts)
        need(path.is_file() and not path.is_symlink(), 'Identity gate failed: missing/symlink input: '+name)
        need(ROOT in path.resolve().parents, 'Identity gate failed: input outside tree')
        content = path.read_bytes()
        need(type(expected) is str and len(expected) == 64 and digest(content) == expected,
             'Identity gate failed: SHA256 mismatch: '+name)
        data[name] = content
    # Extra files cannot silently join this evidence package or import path.
    actual = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*') if p.is_file()}
    need(actual == set(data) | {'verify.py','FROZEN_HASHES.json'},
         'Identity gate failed: file inventory mismatch')
    need('checks.py' in data and 'CHECKS.json' in data, 'Identity gate failed: required files')
    return data

def checked_module(data):
    namespace = {'__name__':'verified_report33_checks','__file__':'checks.py'}
    # Compiling the cached, already-hashed bytes avoids rereading changed code.
    exec(compile(data['checks.py'], 'checks.py', 'exec'), namespace)
    return namespace

def snapshot(root):
    return {p.relative_to(root).as_posix():digest(p.read_bytes())
            for p in sorted(root.rglob('*')) if p.is_file()}

def dump(value):
    return (json.dumps(value, sort_keys=True, indent=2, allow_nan=False)+'\n').encode('utf-8')

def write_external(path, raw):
    if path is None:
        return
    target = pathlib.Path(path).resolve()
    need(target != ROOT and ROOT not in target.parents,
         'Output must be outside the immutable replay directory')
    need(target.parent.is_dir(), 'Output parent must already exist')
    # Never overwrite an existing file, including a symlink target.
    with target.open('xb') as f:
        f.write(raw)

def single(data):
    module = checked_module(data)
    actual = module['run'](data)
    expected = module['read_json'](data['CHECKS.json'])
    need(module['exact'](actual,expected), 'Saved CHECKS.json failed exact-type comparison')
    raw = module['canonical'](actual)
    need(raw == data['CHECKS.json'], 'Saved CHECKS.json is not canonical/reproduced byte-for-byte')
    return raw

def isolated_replay(data):
    before = snapshot(ROOT)
    records = []
    with tempfile.TemporaryDirectory(prefix='report33-supplement-replay-') as temp:
        work = pathlib.Path(temp)
        outputs = []
        for label, options in [('normal', []), ('optimized', ['-O'])]:
            output = work/(label+'.json')
            result = subprocess.run([sys.executable,'-I','-B']+options+
                [str(ROOT/'verify.py'),'--output',str(output)],cwd='/',
                stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=False)
            need(result.returncode == 0, 'Isolated '+label+' replay failed: '+result.stderr.decode())
            raw = output.read_bytes()
            need(raw == data['CHECKS.json'], 'Isolated '+label+' output mismatch')
            outputs.append(raw)
            records.append({'mode':label,'isolated_flag':True,'bytecode_disabled':True,
                            'optimization_flag':bool(options),'working_directory':'/',
                            'exit_code':result.returncode,'checks_sha256':digest(raw)})
        need(outputs[0] == outputs[1], 'Normal/optimized output disagreement')
        # Independently mutate copies; never change this package or original caches.
        tamper = []
        for name in ['checks.py', 'sources/complete75_half_binomial_compiler.py',
                     'evidence/GENERALIZED-COMPILER-SUPPLEMENT.md', 'CHECKS.json']:
            case = work/('tamper-'+str(len(tamper)))
            case.mkdir()
            for rel in before:
                dest=case/rel
                dest.parent.mkdir(parents=True,exist_ok=True)
                dest.write_bytes((ROOT/rel).read_bytes())
            target=case/name
            target.write_bytes(target.read_bytes()+b'\nTAMPERED INVALID EVIDENCE\n')
            result=subprocess.run([sys.executable,'-I','-B','-O',str(case/'verify.py')],
                cwd='/',stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=False)
            need(result.returncode != 0 and
                 ('Identity gate failed: SHA256 mismatch: '+name) in result.stderr.decode(),
                 'Tampered input was not rejected before execution: '+name)
            tamper.append({'modified_file':name,'rejected_before_checker_execution':True,
                           'optimization_flag':True,'exit_code':result.returncode})
    after = snapshot(ROOT)
    need(before == after, 'Replay mutated a packaged source or artifact')
    return dump({'schema':'research-report33-supplement-isolated-replay-v1','status':'PASS',
                 'modes':records,'normal_optimized_outputs_identical':True,
                 'source_tree_byte_hashes_unchanged':True,'tamper_tests':tamper,
                 'network_access_used':False,'upstream_code_executed':False})

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',help='New output file outside this package (never overwritten)')
    parser.add_argument('--replay',action='store_true',help='Run normal/-O isolated children and tamper checks')
    args=parser.parse_args()
    data=identity_gate()
    raw=isolated_replay(data) if args.replay else single(data)
    if args.replay:
        need(raw == data['REPLAY.json'], 'Saved REPLAY.json did not reproduce byte-for-byte')
    write_external(args.output,raw)
    print('PASS: '+('isolated normal/-O replay and 4 fail-closed tamper tests' if args.replay
                   else 'all bounded checks; exact-typed, byte-identical CHECKS.json'))
    return 0

if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (ReplayFailure,OSError,ValueError) as exc:
        print(str(exc),file=sys.stderr)
        raise SystemExit(1)
