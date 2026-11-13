#!/usr/bin/env python3
"""Independently verify retained BFS fixed endpoint header and hash evidence; no Lean replay."""
from pathlib import Path
from hashlib import sha256
from collections import deque
import json
D=Path(__file__).resolve().parents[2]; R=D/'research'; H=R/'direct-bfs-80-ipra-serialized-audit'; O=H/'observations/attempt01'; P=O/'result.json'; RE=H/'observations/reconcile01.json'; F=R/'direct-bfs-80-model-halt-serialized-audit/observations/attempt01/result.json'; B=D/'reviews/ten-positive-80-coherent-rebuilt-closure/observations/attempt01/result.json'; T=R/'direct-bfs-80-ipra-fixed-prototype/observations/directbfs80iprafixed-attempt01/terminal.json'
def sh(p):
 h=sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(4*1024*1024),b''):h.update(b)
 return h.hexdigest()
def j(p):return json.loads(Path(p).read_text())
assert sh(P)=='beca7bfd182f49fb0640ed2b49bff33aa2aa8e1ec09bb1fa1d632b2f06ab9883' and sh(RE)=='446e877a91dcdbec0b590ce7567c76c26c1cca1938c19d571b57f609636202d9'
assert sh(F)=='9591ab25369f57a711315fbee02bd19a360ec4aba15535dc44e85cc983a84003' and sh(B)=='75d4cf43ed4d716b15a13536be5a4cbba96ad03e2249aba7acdc7ace30892276'
a=j(P);r=j(RE);f=j(F);b=j(B);t=j(T); c=a['closure']; A=c['project']; E=c['outside']; F=f['closure']['project']; B=b['selected_project']
assert a['status']=='PASS_CAPTURE' and f['status']=='PASS_CAPTURE' and b['status']=='PASS'
assert sh(T)==a['root_receipt_sha256'] and t['exit']==0 and t['reason'] is None and t['pins']==t['after'] and t['direct_imports']==t['direct_imports_after']
assert sh(Path(t['output_root'])/'DirectBFS80FixedIPRA.olean')==t['object_sha256']==a['root_object_sha256']=='2155f5f05a8e993dc3582f3c14ce9c56916d0ac09dc326c02093d83a878e4703'
assert len(A)==1795 and len(E)==80 and c['header_batches']==66 and len(a['overlaps'])==5 and not a['conflicting_overlaps']
roots=[Path(t['output_root'])]+[Path(x) for x in t['lean_path'].split(':')]+[Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
for group in (A,E):
 for name,row in group.items():
  p=Path(row['path']); assert p.is_file() and sh(p)==row['record']['sha256'] and str(p.resolve())==row['record']['resolved'],name
  rel=Path(name.replace('.','/')+'.olean'); sel=next((q/rel for q in roots if (q/rel).is_file()),None); assert sel is not None and sel.resolve()==p.resolve(),name
  for ext,rec in row['companions'].items():
   q=Path(str(p)[:-6]+ext); assert q.is_file()==(rec is not None),(name,ext)
   if rec is not None: assert str(q.resolve())==rec['resolved'] and sh(q)==rec['sha256'],(name,ext)
seen=set(); leaves=set(); todo=deque(c['roots'])
while todo:
 name=todo.popleft()
 if name in seen or name in leaves:continue
 if name not in A:leaves.add(name);continue
 seen.add(name);todo.extend(A[name]['imports'])
assert seen==set(A) and leaves==set(E)
# Reparse retained Lean reader logs, not a new Lean run.
found={}; paths={row['path']:name for name,row in A.items()}
for i in range(66):
 m=j(O/f'selected-headers-{i:03d}.json'); so=O/f'selected-headers-{i:03d}.stdout'; se=O/f'selected-headers-{i:03d}.stderr'
 assert m['exit']==0 and m['reason'] is None and sh(so)==m['stdout_sha256'] and sh(se)==m['stderr_sha256'] and not se.read_text()
 cmd=m['command'];assert cmd[1:5]==['-M3000','-j1','-DElab.async=false','--run'] and Path(cmd[5]).name=='ReadObjectImports.lean' and 0<len(cmd[6:])<=64
 current=None
 for line in so.read_text().splitlines():
  if line.startswith('BEGIN '):
   q=line[6:];assert current is None and q in cmd[6:] and q in paths and paths[q] not in found;current=paths[q];found[current]=[]
  elif line.startswith('IMPORT ') and current is not None:found[current].append(line[7:])
  elif line=='END' and current is not None:current=None
  else:raise AssertionError((i,line))
 assert current is None
assert found=={n:row['imports'] for n,row in A.items()}
def dig(v):return None if v is None else v['sha256']
def compare(other,shape):
 same=[];different={};absent=[]
 for name,row in sorted(A.items()):
  if name not in other:absent.append(name);continue
  x=row['companions'];y=other[name]['companions'] if shape else other[name]
  delta={k:{'fixed':dig(x.get(k)),'reference':dig(y.get(k))} for k in sorted(set(x)|set(y)) if dig(x.get(k))!=dig(y.get(k))}
  if delta:different[name]=delta
  else:same.append(name)
 return same,different,absent
for ref,shape,key,counts in [(F,True,'against_forward',(739,0,1056)),(B,False,'against_rebuilt80',(1627,2,166))]:
 s,d,z=compare(ref,shape); assert (len(s),len(d),len(z))==counts; assert s==r[key]['same'] and d==r[key]['different'] and z==r[key]['absent']
assert not (set(F)-set(A)) and not r['forward_names_missing_from_fixed']
for name,d in r['against_rebuilt80']['different'].items():
 assert set(d)=={'.olean'}
 print('different',name,'fixed',A[name]['path'],d['.olean']['fixed'],'rebuilt',B[name]['.olean']['path'],d['.olean']['reference'])
 q=Path(B[name]['.olean']['path']);assert sh(q)==d['.olean']['reference']
assert len(a['producer_direct'])==210 and not a['producer_direct_mismatches']
nreceipt=ncompare=0
for name,rs in a['producer_direct'].items():
 for rec in rs:
  p=Path(rec['receipt']);assert sh(p)==rec['receipt_sha256'];src=j(p);assert src['exit']==0 and src['reason'] is None and src['object_sha256']==A[name]['record']['sha256'];nreceipt+=1
  for z in rec['direct_imports_compared']:
   dep=z['module'];row=A.get(dep,E.get(dep));assert row is not None and z['producer_sha256']==z['selected_sha256']==row['record']['sha256'] and z['matches'];assert any(i['module']==dep and i['sha256']==z['producer_sha256'] for i in src['direct_imports']);ncompare+=1
assert ncompare==308
for name,rows in a['overlaps'].items():
 assert len({z['record']['sha256'] for z in rows})==1
 for z in rows:assert sh(z['path'])==z['record']['sha256']
print('PASS 1795 project / 80 external selected object+companion hashes, path selection, captured imports and 66 recorded reader batches')
print('forward 739/739 object+companion equal; rebuilt 1627 equal, 166 absent, 2 different')
print('producer modules',len(a['producer_direct']),'receipt records',nreceipt,'recorded direct comparisons',ncompare,'and five equal-object path overlaps')
print('No independent Lean replay; headers are retained author-reader outputs, and producer, package and dynamic ancestry remain incomplete.')
