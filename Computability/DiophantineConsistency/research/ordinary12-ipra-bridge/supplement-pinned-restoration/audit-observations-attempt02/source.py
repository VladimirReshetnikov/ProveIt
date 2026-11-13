#!/usr/bin/env python3
"""Recheck the restored supplement and its pinned external recipe links."""
from pathlib import Path
import gzip
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
BASE = REPO / 'Computability/DiophantineConsistency'
SUP = BASE / 'con-zfc-diophantine-forms/115-synchronized-exponents/supplement'
PARENT = BASE / 'candidates/free-j-polarized-positive/source/positive/coefficients'
BRIDGE = BASE / 'research/ordinary12-ipra-bridge'
OBS = HERE / 'audit-observations-attempt02'
MANIFEST_SHA = 'b6f7ecd9dc2a6317dce88e01985a1d167e4aef77c393ff8a53c363eece72956d'
VERIFY_SHA = 'd4145136c1b597354fb09b75b9f38e63a74ceb7772b5a64c7f2a04fab69324f7'
RESTORE_SHA = '8f0afdfac74527c41aec98e1f670bb09660cb6f8833198f5f740ea29ad6b58b3'
CHECKS = {
    'beta': ('compact44-retained-beta-byte-prototype/check_payload.py', 'd9f45198470682bb4925bc458ad9fa3ec488a8dffc9d5e8ad9f6f912e08a492b'),
    'K0': ('compact44-k-byte-recipe-prototype/check_recipe.py', '300f474064afaf8451e8874da8a391acb3bc6222cd57956d036d5b5a054b5ba1'),
    'MF': ('compact44-mf-byte-assembly-prototype/check_recipe.py', '24d6c2c9ea3d74a6f94d091d55290f8dbab4dc3fa5dcd24bffd9e8aea8f302d8'),
    'graph': ('free-j-prototype/check_graph.py', '80a76a8fc392f470a56cc00ea45108f15f9b82b882c8356068fc22030ea3e5c0'),
}

def sha(data): return hashlib.sha256(data).hexdigest()
def need(ok, msg):
    if not ok: raise RuntimeError(msg)
def read(p):
    need(p.is_file() and not p.is_symlink(), 'missing/symlink: ' + str(p))
    return p.read_bytes()

need(not OBS.exists(), 'audit output exists')
manifest_raw = read(SUP / 'MANIFEST.json')
need(sha(manifest_raw) == MANIFEST_SHA, 'manifest drift')
manifest = json.loads(manifest_raw)['files']
verification_raw = read(HERE / 'observations/verify.json')
restore_raw = read(HERE / 'observations/restore.json')
need(sha(verification_raw) == VERIFY_SHA and sha(restore_raw) == RESTORE_SHA, 'historic receipts drift')
verification, restoration = json.loads(verification_raw), json.loads(restore_raw)
need(verification['file_count'] == restoration['restored_count'] == 18, 'restoration count')
need(set(verification['mapping']) == set(restoration['files_restored']), 'restoration mapping')
snapshot = {name: read(SUP / name) for name in manifest}
need(all(sha(snapshot[name]) == digest for name, digest in manifest.items()), 'supplement manifest mismatch')
for name, row in verification['mapping'].items():
    src = read(REPO / row['source'])
    need(src == snapshot[name] and sha(src) == row['sha256'] == manifest[name], 'restored source mismatch: ' + name)

child = json.loads(snapshot['circuits/positive12_95_degree70.json'])
parent = json.loads(snapshot['parents/candidates/free-j-polarized-positive/equation.json'])
need(child['coefficient_binding'] == '../coefficients/BINDING.json', 'child binding path')
need(((SUP / 'circuits') / child['coefficient_binding']).resolve(strict=True) == (SUP / 'coefficients/BINDING.json').resolve(strict=True), 'child binding target')
need(child['parent_sha256'] == sha(snapshot['parents/candidates/free-j-polarized-positive/equation.json']), 'child parent pin')
need(child['fixed_numerals'] == parent['fixed_numerals'] == ['beta', 'K0', 'MC', 'MF'], 'port order')
binding = json.loads(snapshot['coefficients/BINDING.json'])
need(snapshot['coefficients/BINDING.json'] == read(PARENT / 'BINDING.json'), 'parent binding differs')
need([binding['ports'][x]['upstream_port'] for x in child['fixed_numerals']] == ['beta', 'K', 'MC', 'MF_source'], 'port mapping')
need('already shifted' in binding['warning'], 'MF shift warning')
for name in child['fixed_numerals']:
    row = binding['ports'][name]
    zipped = snapshot['coefficients/' + row['file']]
    need(zipped == read(PARENT / row['file']) and sha(zipped) == row['sha256_gzip'], 'gzip mismatch: ' + name)
    raw = gzip.decompress(zipped)
    value = int.from_bytes(raw, 'little')
    need(sha(raw) == row['sha256_raw'] and len(raw) == row['raw_bytes'] == (value.bit_length() + 7) // 8 and value.bit_length() == row['bits'], 'raw encoding: ' + name)

# Independently parse the small explicit MC Lean recipe, with source hash pinned.
mc_source = read(BRIDGE / 'compact44-low-byte-complete-recipe/CompactLowByteRecipeData.lean')
need(sha(mc_source) == '6cbe3f43fd7fad8e67b00339a12a468def8fb25eb7f343be675c97fdf155d394', 'MC Lean recipe drift')
text = mc_source.decode()
need('if r = 0 then 254 else if 60 ≤ r then 255 - 2^(67-r) else 255' in text, 'dense rule syntax')
need('if j = 0 then 254 else if denseIndex j then denseWindow ((8*j)%67)' in text, 'byteAt syntax')
part = text.split('def irregularByte (j : ℕ) : ℕ :=\n',1)[1].split('\ndef denseIndex',1)[0]
exceptions = {int(a):int(b) for a,b in re.findall(r'^  if j = (\d+) then (\d+) else$',part,re.M)}
need(len(exceptions) == 11 and part.rstrip().endswith('  255'), 'irregular recipe')
dense_source = text.split('def denseIndex (j : ℕ) : Prop :=\n',1)[1].split('\ninstance',1)[0]
intervals = [(int(a),int(b)) for a,b in re.findall(r'\((\d+) ≤ j ∧ j < (\d+)\)',dense_source)]
need(intervals == [(17,7890),(8233,8308),(8401,8468),(8484,8635)], 'dense intervals')
def byte_at(j):
    r = 8*j % 67
    if j == 0: return 254
    if any(a <= j < b for a,b in intervals): return 254 if r == 0 else 255 - 2**(67-r) if r >= 60 else 255
    return exceptions.get(j,255)
mc = bytes(byte_at(j) for j in range(73759))
need(mc == gzip.decompress(snapshot['coefficients/payloads/MC.bin.gz']), 'MC recipe transcription mismatch')

OBS.mkdir(parents=True)
(OBS/'source.py').write_bytes(read(HERE/'audit.py'))
check_results = {}
for name,(rel,pin) in CHECKS.items():
    script = BRIDGE / rel
    script_before = read(script)
    need(sha(script_before) == pin, 'checker pin: ' + name)
    run = subprocess.run([sys.executable,'-I','-B',str(script)],capture_output=True,text=True,timeout=120)
    (OBS / (name + '.stdout')).write_text(run.stdout)
    (OBS / (name + '.stderr')).write_text(run.stderr)
    need(run.returncode == 0 and not run.stderr and read(script) == script_before, 'checker failed: ' + name)
    check_results[name] = {'exit':run.returncode,'script_sha256':pin,'stdout_sha256':sha(run.stdout.encode())}

# Re-run the original supplement verifier on an isolated full restored copy.
with tempfile.TemporaryDirectory(prefix='supplement-restored-audit-') as tmp:
    copy = Path(tmp) / 'supplement'
    shutil.copytree(SUP,copy,symlinks=True)
    for mode,opts in [('normal',[]),('optimized',['-O'])]:
        run = subprocess.run([sys.executable,'-I','-B',*opts,str(copy/'check.py')],capture_output=True,text=True,timeout=120)
        (OBS / ('supplement-' + mode + '.stdout')).write_text(run.stdout)
        (OBS / ('supplement-' + mode + '.stderr')).write_text(run.stderr)
        need(run.returncode == 0 and not run.stderr, 'supplement verifier failed: ' + mode)
        output = 'CHECK_OPTIMIZED.json' if opts else 'CHECK.json'
        need(sha(read(copy/output)) == manifest[output], 'supplement verifier output drift: ' + mode)
        check_results['supplement_'+mode] = {'exit':run.returncode,'stdout_sha256':sha(run.stdout.encode())}

need(all(read(SUP/name) == data for name,data in snapshot.items()), 'supplement changed')
need(all(read(REPO/row['source']) == snapshot[name] for name,row in verification['mapping'].items()), 'restoration source changed')
need(sha(read(SUP/'MANIFEST.json')) == MANIFEST_SHA, 'manifest changed')
result = {'status':'PASS', 'scope':'external provenance, recipe transcriptions and isolated checker; no Lean filesystem theorem',
          'manifest_sha256':MANIFEST_SHA, 'child_sha256':sha(snapshot['circuits/positive12_95_degree70.json']),
          'parent_sha256':sha(snapshot['parents/candidates/free-j-polarized-positive/equation.json']),
          'binding_sha256':sha(snapshot['coefficients/BINDING.json']),
          'manifest_files_checked':len(manifest), 'restored_files_checked':len(verification['mapping']),
          'restored_bytes':sum(x['size'] for x in verification['mapping'].values()),
          'ports':verification['ports'], 'mc_source_sha256':sha(mc_source),
          'mc_recipe_sha256':sha(mc), 'checks':check_results, 'input_snapshot_unchanged':True}
(OBS/'audit.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS','manifest_files_checked':len(manifest),'restored_files_checked':len(verification['mapping']),
                  'ports':list(binding['ports']),'all_recipe_checks_exit_zero':True},sort_keys=True))
