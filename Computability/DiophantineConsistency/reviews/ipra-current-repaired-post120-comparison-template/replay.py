#!/usr/bin/env python3
"""Provisional source-directed rebase, with no workspace project-object fallback."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import time

D = Path(__file__).resolve().parent
M = D / 'manifest.json'
PKG = Path('/tmp/pra14-full-transitive-2x6o__to/package-lib')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
TOOL = LEAN.parent.parent / 'lib/lean'
SIDECARS = ('.olean','.olean.private','.olean.server','.ir','.olean.hash',
            '.olean.private.hash','.olean.server.hash','.ir.hash','.ilean','.ilean.hash')
EXT = {'Foundation','Mathlib','Lean','Init','Std','Batteries','Qq','Aesop',
       'Plausible','ProofWidgets','ImportGraph','LeanSearchClient','Lake'}
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
raw = M.read_bytes()
mh = hashlib.sha256(raw).hexdigest()
assert len(sys.argv) == 2 and sys.argv[1] == mh
m = json.loads(raw)
assert m['status'] == 'PROVISIONAL_REBASE_INPUT' and H(__file__) == m['driver_sha256']
SM, SNAP = Path(m['candidate_survey_path']), Path(m['snapshot_root'])
assert H(SM) == m['candidate_survey_sha256']
survey = json.loads(SM.read_text())
P, R = Path(m['parent_state_path']).parent, Path(m['workspace_root'])
assert H(P/'state.json') == m['parent_state_sha256']
assert json.loads((P/'state.json').read_text())['status'] == 'PASS'
assert len(survey['sources']) == 1099 and m['order'] == survey['order']
assert len(m['workspace_sources']) == 1104 and m['target'] == survey['target'] == m['order'][-1]
assert len(m['order']) == len(set(m['order']))
dirty = set(m['order'])
excluded = {name.replace('.', '/') + suffix for name in dirty for suffix in SIDECARS}

def inventory(root):
    out = {}
    for d, _, files in os.walk(root / 'lib', followlinks=True):
        for name in files:
            if name.endswith(SIDECARS):
                p = Path(d) / name
                out[str(p.relative_to(root / 'lib'))] = {'sha256': H(p), 'resolved_path': str(p.resolve())}
    return out

def external():
    assert set(m['parent_external_direct_paths']) == set(m['parent_external_resolved_paths'])
    for path, h in m['parent_external_direct_paths'].items():
        assert H(path) == h and str(Path(path).resolve()) == m['parent_external_resolved_paths'][path]
    assert all(not os.path.lexists(p) for p in m['parent_external_absent_paths'])
    for name, row in survey['external'].items():
        rel = name.replace('.', '/') + '.olean'
        p = next((q for q in (PKG / rel, TOOL / rel) if q.is_file()), None)
        assert p is not None and str(p.resolve()) == row['selected'], name
        for path, item in row['companions'].items():
            if item is None: assert not os.path.lexists(path), path
            else: assert Path(path).is_file() and str(Path(path).resolve()) == item['realpath'] and H(path) == item['sha256'], path
    for path, item in m['fallback_companions'].items():
        if item is None: assert not os.path.lexists(path), path
        else: assert Path(path).is_file() and str(Path(path).resolve()) == item['realpath'] and H(path) == item['sha256'], path
    for path, item in m['inherited_fallback_companions'].items():
        if item is None: assert not os.path.lexists(path), path
        else: assert Path(path).is_file() and str(Path(path).resolve()) == item['realpath'] and H(path) == item['sha256'], path

def frozen():
    assert H(M) == mh and H(__file__) == m['driver_sha256'] and H(D/'prepare.py') == m['preparer_sha256']
    assert H(SM) == m['candidate_survey_sha256'] and H(P/'state.json') == m['parent_state_sha256'] and H(LEAN) == m['lean_sha256']
    assert all(str(Path(p).resolve()) == p and H(p) == h for p,h in m['gate_guard'].items())
    assert all(str(Path(p).resolve()) == p and H(p) == h for p,h in m['origin_guard'].items())
    for name, row in survey['sources'].items():
        p = SNAP / (name.replace('.', '/') + '.lean')
        assert p.is_file() and not p.is_symlink() and p.resolve() == p.absolute() and H(p) == row['sha256'], name
    assert inventory(P) == m['parent_inventory']
    external()

seen = set()
for name in m['order']:
    actual = re.findall(r'^import\s+([A-Z][\w.]*)', (SNAP/(name.replace('.', '/')+'.lean')).read_text(), re.M)
    assert actual == survey['sources'][name]['imports']
    assert all(dep not in dirty or dep in seen for dep in actual)
    seen.add(name)
frozen()
w = Path(tempfile.mkdtemp(prefix='ipra-post120-replay-'))
lib, logs = w/'lib', w/'logs'
lib.mkdir(); logs.mkdir()
(w/'manifest.json').write_bytes(raw)
(w/'driver.py').write_bytes(Path(__file__).read_bytes())
for rel, row in m['parent_inventory'].items():
    if rel not in excluded:
        dst = lib/rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.symlink_to(row['resolved_path'])

def drift():
    out=[]
    for name,row in m['workspace_sources'].items():
        p=R/row['path']
        try: actual=H(p) if p.is_file() else None
        except OSError: actual=None
        if actual != row['sha256']: out.append({'module':name,'expected':row['sha256'],'actual':actual})
    return out

state={'status':'RUNNING','manifest_sha256':mh,'survey_manifest_sha256':m['candidate_survey_sha256'],
       'driver_sha256':m['driver_sha256'],'parent_state_sha256':m['parent_state_sha256'],
       'records':[],'workspace_drift_before':drift(),'boundary':m['boundary']}
def save():
    (w/'state.json').write_text(json.dumps(state,sort_keys=True,indent=2)+'\n')

def audit():
    frozen()
    assert H(w/'manifest.json') == mh and H(w/'driver.py') == m['driver_sha256']
    expected={rel:row for rel,row in m['parent_inventory'].items() if rel not in excluded}
    for row in state['records']:
        if row['exit'] == 0:
            name=row['name']; obj=lib/(name.replace('.', '/')+'.olean')
            assert obj.is_file() and not obj.is_symlink() and obj.resolve()==obj.absolute()
            expected[name.replace('.', '/')+'.olean']={'sha256':row['object_sha256'],'resolved_path':str(obj.absolute())}
            assert H(logs/(name.replace('.', '_')+'.log'))==row['log_sha256']
            for dep,entry in row['direct_imports'].items():
                p=Path(survey['external'][dep]['selected']) if dep.split('.')[0] in EXT else lib/(dep.replace('.', '/')+'.olean')
                assert p.exists() and str(p.resolve())==entry['resolved_path'] and H(p)==entry['sha256']
    assert inventory(w)==expected

def warnings(text):
    out=[]
    tests=[('unused_simp',r'^This simp argument is unused:'),
           ('unused_section',r'^automatically included section variable\(s\) unused in theorem '),
           ('unused_variable',r'^Variable name `[^`]+` is not explicitly referenced\.$'),
           ('simp_suggestion',r"^(?:try 'simp' instead of 'simpa'|Try `simp at this` instead of `simpa using this`)$"),
           ('noop_tactic',r"^'.+' tactic does nothing$"),('unreachable_tactic',r'^this tactic is never executed$'),
           ('deprecation',r'^`[^`]+` has been deprecated(?:[.:].*)?$'),
           ('simp_discrimination',r'^Left-hand side of simp theorem is headed by a `\.other` key in the discrimination tree'),
           ('tactic_sequence',r'^Used `tac1 <;> tac2` where `\(tac1; tac2\)` would suffice$'),
           ('exponent_threshold_notice',r'^exponent [0-9]+ exceeds the threshold [0-9]+, exponentiation operation was not evaluated, use `set_option exponentiation.threshold <num>` to set a new threshold$')]
    for line in text.splitlines():
        if 'warning:' not in line: continue
        msg=line.split('warning:',1)[1].strip()
        hits=[category for category,pattern in tests if re.search(pattern,msg)]
        assert len(hits)==1, ('unrecognized warning',line)
        out.append({'category':hits[0], 'message':msg, 'full_line':line})
    return out

save(); print('PRIVATE',w,flush=True)
try:
    audit()
    env=dict(os.environ,LEAN_PATH=str(lib)+':'+str(PKG),LEAN_NUM_THREADS='1')
    env.pop('LEAN_SRC_PATH',None)
    for name in m['order']:
        obj=lib/(name.replace('.', '/')+'.olean'); obj.parent.mkdir(parents=True,exist_ok=True)
        log=logs/(name.replace('.', '_')+'.log'); direct={}; start=time.monotonic()
        for dep in survey['sources'][name]['imports']:
            p=Path(survey['external'][dep]['selected']) if dep.split('.')[0] in EXT else lib/(dep.replace('.', '/')+'.olean')
            assert p.exists(),str(p)
            direct[dep]={'sha256':H(p),'resolved_path':str(p.resolve())}
        with log.open('w') as out:
            proc=subprocess.run([str(LEAN),'-M8000','-j1','-DElab.async=false','--root='+str(SNAP),
                                 str(SNAP/(name.replace('.', '/')+'.lean')),'-o',str(obj)],
                                cwd=R,env=env,stdout=out,stderr=subprocess.STDOUT)
        row={'name':name,'exit':proc.returncode,'object_sha256':H(obj) if obj.exists() else None,
             'log_sha256':H(log),'direct_imports':direct,'seconds':time.monotonic()-start}
        state['records'].append(row);save();print(name,proc.returncode,flush=True)
        text=log.read_text()
        assert proc.returncode==0 and 'error:' not in text and 'sorryAx' not in text and not re.search(r'\b(?:sorry|admit)\b',text)
        row['warnings']=warnings(text);save()
        if name==m['target']:
            reports=re.findall(r'depends on axioms: \[([^\]]*)\]',text)
            assert len(reports)==2 and all(set(x.strip() for x in block.split(','))=={'propext','Classical.choice','Quot.sound'} for block in reports), (text,reports)
    audit()
    state['workspace_drift_after']=drift()
    state['source_matches_workspace_at_final_check']=not state['workspace_drift_after']
    state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as exc:
    state.update(status='FAILED',failure=repr(exc));save();raise
