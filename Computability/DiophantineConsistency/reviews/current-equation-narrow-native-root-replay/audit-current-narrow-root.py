from pathlib import Path
import hashlib,json,re,subprocess
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews';D=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
p=V/'current-equation-narrow-dependency-replay.json';d=json.loads(p.read_text());a=d['exact_move_audit'];result=[]
for e in d['pins']+d['bundle_files']:
 q=R/Path(e['path']);assert sha(q)==e['sha256'],str(q)
for key in ['parent','native_inventory']:assert sha(d[key])==d[key+'_sha256']
newtexts=[(D/(e['module']+'.lean')).read_text()for e in a['new_sources']]
for e in a['new_sources']:assert sha(D/(e['module']+'.lean'))==e['sha256']
imports=dict(LowMaskCoding='LowMaskData',WangTiles942Core='WangTiles942TableData',CurrentMasks2011='CurrentMaskData2011',CurrentKernel2011='CurrentKernelData2011',CurrentWindowCarry2011='CurrentKernelData2011',ObjectCurrentEquation2011='CurrentEquationSyntax2011',ArithmeticCurrentEquation2011='CurrentEquationSyntax2011')
for e in a['old_sources']:
 q=D/(e['module']+'.lean');old=subprocess.check_output(['git','show',a['snapshot']+':'+str(q.relative_to(R))],cwd=R).decode();assert hashlib.sha256(old.encode()).hexdigest()==e['old_sha256']==sha(e['snapshot'])
 moves=[x for x in a['moves']if x['owner']==e['module']];spans=[]
 for x in moves:
  t=x['text'];assert hashlib.sha256(t.encode()).hexdigest()==x['sha256'];assert old.count(t)==1;assert sum(t in s for s in newtexts)==1;pos=old.index(t);spans.append((pos,pos+len(t)))
 spans.sort();assert all(b<=c for(_,b),(c,_)in zip(spans,spans[1:]))
 left=old
 for lo,hi in reversed(spans):left=left[:lo]+left[hi:]
 expected='import DiophantineConsistency.'+imports[e['module']]+'\n'+left
 # Authorized formatting change collapses blank lines after declaration removals.
 normalized=lambda s:re.sub(r'\n{3,}','\n\n',s)
 assert normalized(q.read_text())==normalized(expected),e['module'];assert sha(q)==e['new_sha256'];result.append(dict(owner=e['module'],exact_declarations=len(moves),all_other_nonblank_source_bytes_unchanged=True))
out=dict(status='PASS',packet_sha256=sha(p),snapshot=a['snapshot'],exact_move_count=len(a['moves']),owners=result,extra_pins=len(d['pins'])+len(d['bundle_files'])+2,driver_sha256=sha(__file__))
Path('/tmp/current-narrow-root-move-audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
