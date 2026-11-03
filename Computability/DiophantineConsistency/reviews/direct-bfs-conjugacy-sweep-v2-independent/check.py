#!/usr/bin/env python3
"""Independent finite source/receipt audit; does not invoke Lean."""
from pathlib import Path
from hashlib import sha256
import ast, json, re, shutil, subprocess, sys, tempfile
D=Path(__file__).resolve().parents[2]; R=D/'research'; P=R/'direct-bfs-lean-conjugacy-coverage-prototype'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def j(p):return json.loads(Path(p).read_text())
runner='81e70123d07fa99d907459ad080cfd059c622f66a7fe4f69e8e340a3e2bef91c'; manifest='d0847a6276885e969d06cf6c2f3f64b1de1f1cfba71095e35c33393630a57392'; gen='54b48b7926b5207767380d7810806f1029dbb4ce534527cc9e318a54981d3b25'
assert sha(P/'run-chunks-v2.py')==runner and sha(P/'coverage-manifest-v2.json')==manifest and sha(P/'generate-v2.py')==gen
m=j(P/'coverage-manifest-v2.json'); records=m['records']; assert len(records)==59 and m['chunk_size']==16
sizes={'rows':943,'inverse':943,'horizontal':250,'vertical':439,'inversebounds':943,'horizontalbounds':250,'verticalbounds':439}
for i,r in enumerate(records):
 assert r['index']==i and r['module']==f'DirectBFSCoverage{i:03d}' and sha(P/'chunks-v2'/(r['module']+'.lean'))==r['source_sha256']
 start=i*16
 kinds=['rows','inverse']+(['horizontal'] if start<250 else [])+(['vertical'] if start<439 else [])
 expected=[{'kind':k,'start':start,'count':min(16,sizes[k]-start)} for k in kinds]+[{'kind':k+'bounds','start':start,'count':min(16,sizes[k]-start)} for k in kinds if k!='rows']
 assert r['ranges']==expected
for kind,end in sizes.items(): assert [x for r in records for a in r['ranges'] if a['kind']==kind for x in range(a['start'],a['start']+a['count'])]==list(range(end))
with tempfile.TemporaryDirectory(prefix='independent-conjugacy-gen-') as temp:
 t=Path(temp);shutil.copyfile(P/'generate-v2.py',t/'generate-v2.py')
 subprocess.run([sys.executable,'-I','-S','-B',str(t/'generate-v2.py')],check=True,stdout=subprocess.PIPE)
 assert (t/'coverage-manifest-v2.json').read_bytes()==(P/'coverage-manifest-v2.json').read_bytes()
 assert sorted(x.name for x in (t/'chunks-v2').iterdir())==sorted(x.name for x in (P/'chunks-v2').iterdir())
 for q in (t/'chunks-v2').iterdir():assert q.read_bytes()==(P/'chunks-v2'/q.name).read_bytes()
base=(R/'direct-bfs-lean-conjugacy-base-prototype/DirectBFSConjugacyBase.lean').read_text()
a={}
for name in ('horizontal','horizontalInverse','vertical','verticalInverse','rowMap','rowInverse'):
 hit=re.search(r'^def '+name+r' : Array Nat := #\[(.*)\]$',base,re.M);assert hit
 a[name]=ast.literal_eval('['+hit.group(1)+']')
for f,iv,n in [('horizontal','horizontalInverse',250),('vertical','verticalInverse',439),('rowMap','rowInverse',943)]:
 x,y=a[f],a[iv];assert len(x)==len(y)==n and all(0<=z<n for z in x+y)
 assert all(x[y[i]]==i and y[x[i]]==i for i in range(n))
old=(R/'ordinary12-ipra-bridge/compact44-943-table-prototype/Compact943Data.lean').read_text().split('-- BEGIN PINNED ORDERED ROWS\n')[1].split('\n-- END PINNED ORDERED ROWS')[0]
old=ast.literal_eval('['+old+']')
direct=(R/'direct-bfs-lean-kernel-prototype/DirectBFSSymbolicKernel.lean').read_text().split('def rows : List (Nat × Nat × Nat × Nat) := [\n')[1].split('\n  ]')[0]
direct=ast.literal_eval('['+direct+']')
assert len(old)==len(direct)==943
h,v,rm=a['horizontal'],a['vertical'],a['rowMap']
for i,(w,n,e,s) in enumerate(old):assert (h[w],v[n],h[e],v[s])==direct[rm[i]]
for pilot,i in [('pilot03',0),('pilot04',58)]:
 ob=P/'observations'/pilot;pl=j(ob/'plan.json');res=j(ob/'result.json'); st=ob/f'stage-{i:03d}';term=j(st/'terminal.json');r=records[i]
 assert pl['runner_sha256']==res['runner_sha256']==term['runner_sha256']==runner
 assert pl['manifest_sha256']==res['manifest_sha256']==manifest
 assert (pl['start'],pl['stop'],res['start'],res['stop'],res['stages'],res['status'])==(i,i+1,i,i+1,1,'PASS_CHUNK_RANGE')
 assert term['exit']==0 and term['accepted'] and term['reason'] is None and term['ranges']==r['ranges']
 assert sha(st/'source.lean')==term['source_sha256']==r['source_sha256']
 assert sha(st/'stdout')==term['stdout_sha256'] and sha(st/'stderr')==term['stderr_sha256'] and sha(term['object_path'])==term['object_sha256']
 assert term['direct_import']==pl['selected_import'] and sha(term['direct_import']['path'])==term['direct_import']['sha256']=='c5b92d5de73775bd9e0e6ef507ba903fd68d093404ab5d30bd64d0af7cdfc36d'
 selected=next(Path(x)/'DirectBFSConjugacyChunk.olean' for x in pl['lean_path'].split(':') if (Path(x)/'DirectBFSConjugacyChunk.olean').is_file())
 assert selected.resolve()==Path(term['direct_import']['path']).resolve()
 assert len(term['preflight']['lean'])<2 and term['preflight']['available_kib']>=8*1024**2
 assert all(len(s['lean'])<=2 and s['available_kib']>=8*1024**2 for s in term['samples'])
 assert term['elapsed']<100 and term['command'][1:4]==['-M3000','-j1','-DElab.async=false']
 logs=(st/'stdout').read_text()+(st/'stderr').read_text()
 for x in r['ranges']:assert logs.count(f"'DirectBFSCoverage.{x['kind']}_{i:03d}' does not depend on any axioms")==1
 assert not re.search(r'\b(?:error|warning)(?:\([^)]*\))?:|sorryAx',logs)
 print(pilot,'stage',i,'object',term['object_sha256'],'elapsed',round(term['elapsed'],2),'samples',len(term['samples']))
print('manifest disjoint coverage',sizes,'chunks',len(records))
print('all arrays bounded; both inverse compositions; all 943 source-row conjugacies checked')
print('fixed starts',{'row_0_1':[rm[x] for x in range(2)],'h_0_5':[h[x] for x in range(6)],'v_0_1':[v[x] for x in range(2)],'v_432_438':[v[x] for x in range(432,439)]})
print('PASS: independent finite checks; no Lean replay or full ancestry authentication')
