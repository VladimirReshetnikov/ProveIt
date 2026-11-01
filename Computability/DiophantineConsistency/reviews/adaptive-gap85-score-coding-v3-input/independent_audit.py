#!/usr/bin/env python3
"""Independently audit the frozen v3 comparison and retained overlay paths."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

D=Path(__file__).resolve().parent
if len(sys.argv)!=2:raise SystemExit('usage: independent_audit.py REPLAY_PACKET')
O=Path(sys.argv[1]);m=json.loads((D/'manifest.json').read_text());r=json.loads((O/'comparison.json').read_text())
rm=json.loads(Path(m['repair_manifest']).read_text());H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert r['status']=='MATCHED_PASS' and r['manifest_sha256']==H(D/'manifest.json') and r['compare_sha256']==H(D/'compare.py')
def validate(path,expected):
    p=Path(path)
    if expected is None:
        assert not os.path.lexists(p),path
    else:
        assert p.exists(),path
        assert str(p.resolve())==expected['resolved'],path
        if expected['kind']=='symlink':assert p.is_symlink() and os.readlink(p)==expected['target'],path
        elif expected['kind']=='file':assert p.is_file() and not p.is_symlink(),path
        elif expected['kind']=='directory':assert p.is_dir() and not p.is_symlink(),path
        else:raise AssertionError(('unknown kind',path))
        if 'sha256' in expected:assert p.is_file() and H(p)==expected['sha256'],path
for path,expected in m['guard'].items():validate(path,expected)
for table in (m['provider_companions'],m['score_candidates']):
    for path,expected in table.items():validate(path,expected)
for path,expected in rm['guard'].items():assert H(path)==expected,path
for table in rm['candidates'].values():
    for path,expected in table.items():
        p=Path(path)
        if expected is None:assert not os.path.lexists(p),path
        else:assert p.is_file() and str(p.resolve())==expected['resolved'] and H(p)==expected['sha256'],path
provider=Path(m['provider'])
assert {p.name for p in (provider/'lib').iterdir()}==set(m['provider_root'])
assert {p.name for p in (provider/'lib/DiophantineConsistency').iterdir()}==set(m['provider_project'])
for name,entry in m['provider_root'].items():validate(provider/'lib'/name,entry)
for name,entry in m['provider_project'].items():validate(provider/'lib/DiophantineConsistency'/name,entry)
rows=r['records'];assert len(rows)==2
for label in ('author','peer'):
    packet=O/label;state=json.loads((packet/'state.json').read_text());root=Path(r[label])
    assert H(packet/'state.json')==r[label+'_state_sha256'] and state['status']=='PASS'
    assert state['records']==rows and [x['stage'] for x in state['direct_checks']]==r['direct_stages']
    for row in rows:
        n=row['module'];assert row['exit']==0 and row['warnings']==0
        for folder,ext,key in (('sources','.lean','source_sha256'),('objects','.olean','object_sha256'),('logs','.log','log_sha256')):
            path=packet/folder/(n+ext);assert H(path)==row[key]
    assert H(packet/'sources/AdaptiveGap85ScoreCoding.lean')==m['score_source_sha256']
    assert H(packet/'sources/AdaptiveGap85ScoreCodingChecks.lean')==m['checks_source_sha256']
    # Enumerate the current private overlay independently without following its
    # directory symlinks. The run state recorded all entries and their targets.
    observed={}
    for d,dirs,files in os.walk(root/'lib',followlinks=False):
        for name in dirs+files:
            p=Path(d)/name;observed[str(p.relative_to(root/'lib'))]=p
    assert set(observed)==set(state['overlay_final'])
    for rel,p in observed.items():validate(p,state['overlay_final'][rel])
    env=dict(os.environ,LEAN_PATH=':'.join([str(root/'lib'),*m['roots'][1:]]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
    for name in ('AdaptiveGap85ScoreCoding','AdaptiveGap85ScoreCodingChecks'):
        f=root/'src/DiophantineConsistency'/(name+'.lean')
        cmd=[m['lean'],'--deps','--root='+str(root/'src'),str(f)]
        result=subprocess.run(cmd,cwd=m['root'],env=env,capture_output=True,text=True,check=True)
        actual=result.stdout.splitlines();saved=state['direct_checks'][-1]['main' if name=='AdaptiveGap85ScoreCoding' else 'checks']
        assert not result.stderr and actual==[x['logical'] for x in saved]
        for item in saved:validate(item['logical'],item['entry'])
    assert state['direct_checks'][0]['checks'][-1]['entry'] is None
    assert state['direct_checks'][-1]['checks'][-1]['entry']['sha256']==rows[0]['object_sha256']
result={'status':'PASS','manifest_sha256':H(D/'manifest.json'),'comparison_sha256':H(O/'comparison.json'),
        'auditor_sha256':H(__file__),'rows':len(rows),'overlay_entries':r['overlay_entries_final'],
        'provider_companions':len(m['provider_companions']),'score_candidates':len(m['score_candidates']),
        'cantor_candidates':sum(map(len,rm['candidates'].values())),
        'scope':'Rechecks retained v3 artifacts and current direct resolutions; transitive and dynamic ancestry remains inherited.'}
(O/'independent-audit.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print('PASS independent v3 audit:',len(rows),'rows;',r['overlay_entries_final'],'overlay entries')
