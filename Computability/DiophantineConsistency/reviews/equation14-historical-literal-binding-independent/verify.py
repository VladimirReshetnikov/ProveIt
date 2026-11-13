#!/usr/bin/env python3
"""Rerun the finite 14-variable binding checks and the Lean port computation.

This is external finite verification, not Lean semantics for TeX/PDF or a
replay of the object-theory endpoint. It keeps all historical-provider,
manual-recipe, package-transitive and dynamic-loading limitations.
"""
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

if not __debug__:
    raise RuntimeError('This audit requires assertions; do not run Python with -O or -OO')
sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
BASE = HERE.parents[1]
PACKET = BASE/'reviews/equation14-historical-literal-binding'
PARENT = Path('/tmp/ipra-aq29-fresh-project-pair/author')
PROVIDER = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
SNAP = Path('/tmp/ipra-aq29-fresh-source-closure-v2')
TRIAL = Path('/tmp/ipra-standard-current14-author-trial')
PROBE = Path('/tmp/equation14-fixed-port-probe')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
GRAPH = BASE/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()

inputs = [Path(__file__), PACKET/'audit_expression.py', PACKET/'audit_ports.py',
          PACKET/'Probe.lean', PACKET/'expression-receipt.json', PACKET/'ports-receipt.json',
          PACKET/'terminal-observation.json', PACKET/'printed-constants-repeat.json',
          PACKET/'deps.log', PACKET/'probe.log', GRAPH, BASE/'equation.tex', BASE/'equation.pdf',
          BASE/'research/adaptive-direct-ordinate86/verify_display_tex14.py',
          BASE/'research/adaptive-direct-ordinate86/verify_display_tex86.py',
          BASE/'research/adaptive-direct-ordinate86/verify_printed_constants86.py',
          BASE/'research/adaptive-direct-ordinate86/PRINTED-CONSTANTS-AUDIT.json',
          BASE/'equation86.tex', PARENT/'state.json', SNAP/'manifest.json', TRIAL/'state.json',
          TRIAL/'src/DiophantineConsistency/IPRACurrentNativeZFC.lean',
          TRIAL/'src/DiophantineConsistency/IPRAStandardCurrentEndpoint.lean',
          PARENT/'lib/DiophantineConsistency/CurrentKernelData2011.olean',
          PROBE/'Probe.lean', PROBE/'probe.log', PROBE/'deps.log', PROBE/'printed-constants-repeat.json',
          PROVIDER/'Init.olean', LEAN]
inputs += [PACKET/'port-outputs'/f'port{i}.txt.gz' for i in range(4)]
inputs += [PROBE/f'port{i}.txt' for i in range(4)]
candidate = json.loads(GRAPH.read_text())
inputs += [GRAPH.parent/'coefficients'/candidate['coefficient_binding']['ports'][name]['file']
           for name in candidate['fixed_numerals']]
parent_manifest = json.loads((SNAP/'manifest.json').read_text())
pending = ['DiophantineConsistency.CurrentEquationSyntax2011']; closure = set()
while pending:
    name = pending.pop()
    if name in closure: continue
    closure.add(name)
    pending.extend(x for x in parent_manifest['sources'][name]['imports']
                   if x in parent_manifest['sources'] and x not in closure)
assert len(closure) == 24
workspace_root = BASE.parents[1]
for name in closure:
    row=parent_manifest['sources'][name]
    inputs += [SNAP/row['snapshot_path'], workspace_root/row['workspace_path']]
recipe_sources = json.loads((PACKET/'printed-constants-repeat.json').read_text())['source_sha256']
inputs += [BASE/name for name in recipe_sources]
before = {str(p.resolve()): H(p) for p in inputs}
prior_expression = json.loads((PACKET/'expression-receipt.json').read_text())
prior_ports = json.loads((PACKET/'ports-receipt.json').read_text())
terminal = json.loads((PACKET/'terminal-observation.json').read_text())
assert terminal['expression_binding']['observed_exit_code'] == 0
assert terminal['lean_direct_port_probe']['observed_exit_code'] == 0
assert terminal['exact_full_integer_comparison']['observed_exit_code'] == 0
assert terminal['printed_recipe_reconstruction']['repeat_observed_exit_code'] == 0

def command(args, cwd=None, env=None, timeout=240):
    r = subprocess.run(args, cwd=cwd, env=env, text=True, capture_output=True, timeout=timeout)
    return {'exit':r.returncode, 'stdout':r.stdout, 'stderr':r.stderr}

optimized = {}
for name in ('audit_expression.py','audit_ports.py'):
    for flag in ('-O','-OO'):
        r = command([sys.executable,flag,str(PACKET/name)])
        assert r['exit'] != 0 and 'This audit requires assertions' in r['stderr'], (name,flag,r)
        optimized[name+':'+flag] = {'exit':r['exit'], 'guard_observed':True}

# Copy the audited inputs to a disposable sibling directory. This preserves
# their relative repository layout while leaving both historical receipts alone.
with tempfile.TemporaryDirectory(prefix='.eq14-independent-',dir=PACKET.parent) as td:
    tmp = Path(td)
    for name in ('audit_expression.py','audit_ports.py','Probe.lean','probe.log','deps.log','printed-constants-repeat.json'):
        shutil.copyfile(PACKET/name,tmp/name)
    shutil.copytree(PACKET/'port-outputs',tmp/'port-outputs')
    results = {}
    for name,out,prior in [('audit_expression.py','expression-receipt.json',prior_expression),
                           ('audit_ports.py','ports-receipt.json',prior_ports)]:
        r = command([sys.executable,str(tmp/name)])
        assert r['exit'] == 0, (name,r)
        receipt=json.loads((tmp/out).read_text())
        assert receipt == prior, (name,'changed result')
        results[name]={'exit':r['exit'],'receipt_sha256':H(tmp/out),'stdout':r['stdout'].strip()}

    # Repeat the direct computation independently, never writing to the old
    # probe directory or modifying its captured outputs.
    probe_dir = tmp/'lean-probe'; probe_dir.mkdir()
    shutil.copyfile(PACKET/'Probe.lean',probe_dir/'Probe.lean')
    env = dict(os.environ,LEAN_PATH=str(PARENT/'lib')+':'+str(PROVIDER),LEAN_NUM_THREADS='1')
    for key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):
        env.pop(key,None)
    deps=command([str(LEAN),'--deps',str(probe_dir/'Probe.lean')],cwd=probe_dir,env=env)
    assert deps['exit']==0 and not deps['stderr'] and deps['stdout']==(PACKET/'deps.log').read_text(),deps
    run=command([str(LEAN),'-M2500','-j1','-DElab.async=false','--root='+str(probe_dir),
                 str(probe_dir/'Probe.lean')],cwd=probe_dir,env=env,timeout=240)
    assert run['exit']==0 and run['stdout']=='WROTE_FOUR_EXACT_DECIMAL_PORTS\n' and not run['stderr'],run
    ports=[]
    for i,name in enumerate(candidate['fixed_numerals']):
        got=(probe_dir/f'port{i}.txt').read_bytes()
        saved=gzip.decompress((PACKET/'port-outputs'/f'port{i}.txt.gz').read_bytes())
        meta=candidate['coefficient_binding']['ports'][name]
        binary=gzip.decompress((GRAPH.parent/'coefficients'/meta['file']).read_bytes())
        assert got==saved==str(int.from_bytes(binary,'big')).encode('ascii')
        ports.append({'name':name,'digits':len(got),'decimal_sha256':hashlib.sha256(got).hexdigest(),
                      'integer_sha256':hashlib.sha256(binary).hexdigest()})

# Rerun the original independent finite recipe reconstruction. The result
# checks a pinned TeX block but remains a manually transcribed recipe.
recipe=command([sys.executable,str(BASE/'research/adaptive-direct-ordinate86/verify_printed_constants86.py')],
               cwd=BASE,timeout=240)
assert recipe['exit']==0,recipe
reconstructed=json.loads(recipe['stdout'])
old=json.loads((PACKET/'printed-constants-repeat.json').read_text())
prior_86=old['source_sha256'].pop('equation86.tex')
current_86=reconstructed['source_sha256'].pop('equation86.tex')
assert reconstructed==old
assert reconstructed['rank_comparisons']==885481 and reconstructed['tile_rows']==942

after={str(p.resolve()):H(p) for p in inputs}
assert after==before
report={'status':'PASS_INDEPENDENT_FINITE_BINDING_REVIEW', 'input_sha256':before,
        'guarded_script_reruns':results,'optimized_python_negative_controls':optimized,
        'fresh_probe_exit':run['exit'],'fresh_probe_stdout':run['stdout'].strip(),
        'fresh_probe_deps_exit':deps['exit'],'ports':ports,
        'recipe_rerun_exit':recipe['exit'],'recipe_rank_comparisons':reconstructed['rank_comparisons'],
        'recipe_tile_rows':reconstructed['tile_rows'],
        'recipe_equation86_hash_at_original_repeat':prior_86,'recipe_equation86_hash_now':current_86,
        'scope':'Finite parsed arithmetic and byte-reproduced PDF; independent Lean #eval and external integer comparisons. TeX fixed decoder/table/rank/port recipes remain manually transcribed, not parsed; no formal PDF semantics, endpoint Lean replay, or full package/dynamic provenance is claimed.'}
out=HERE/'receipt.json'
if out.exists(): raise RuntimeError('refusing to overwrite evidence')
out.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print(report['status'],H(out))
