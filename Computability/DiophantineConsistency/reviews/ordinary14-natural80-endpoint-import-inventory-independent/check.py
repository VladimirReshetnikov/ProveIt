#!/usr/bin/env python3
"""Independently inspect pinned 80-endpoint lexical source evidence; no Lean."""
from collections import deque
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary14-natural80-endpoint-import-inventory'
def pin(p,h):
 b=p.read_bytes(); assert hashlib.sha256(b).hexdigest()==h,str(p);return b
inv=json.loads(pin(P/'inventory.json','47677589f08a55c6d8a46c5801476c4ffc5ffd64299ef7d1b19017eb86b09301'))
tok=json.loads(pin(P/'tokens.json','06a7236af61be2da7bd30c9e97d25328c0f52df585d28799e8fce6a0fd1e854f'))
prior=json.loads(pin(D/'research/ordinary14-natural81-endpoint-import-inventory/inventory.json','bfb90445976aed586a849295ddd5afa5c706b7da7c8b6519bb2bd022491e5f40'))
slim=json.loads(pin(D/'research/ordinary14-root74-slim-overlay/inventory.json','b3317a1aa674fd67708aef94685af953126fcd1f30ead3bd43a9afb95467583e'))
rows=inv['drafts_topological']; assert len(rows)==184 and len({r['module'] for r in rows})==184
by={r['module']:r for r in rows}; order={r['module']:i for i,r in enumerate(rows)}
old={r['module']:r for r in prior['drafts_topological']}; shared=set(by)&set(old)
assert len(shared)==173 and set(old)<=set(by) and len(set(by)-set(old))==11
assert all(by[n]['sha256']==old[n]['sha256'] for n in shared)
sp={r['module']:r for r in slim['drafts_topological']}; assert len(set(by)&set(sp))==158 and len(set(by)-set(sp))==26 and set(sp)-set(by)=={'Root74Endpoint'}
assert all(by[n]['sha256']==sp[n]['source_sha256'] for n in set(by)&set(sp))
qualified=set(); files={}
for row in rows:
 path=D/row['path'];b=pin(path,row['sha256']);files[row['path']]=b.decode(); assert path.stem==row['module']
 heads=[]
 for line in b.decode().splitlines():
  if not line.strip(): continue
  m=re.fullmatch(r'import\s+([A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*)\s*',line)
  if not m:break
  heads+=m.group(1).split()
 bare=[x for x in heads if '.' not in x];q=[x for x in heads if '.' in x]
 assert bare==row['bare_imports'] and q==row['qualified_imports']
 for n in bare: assert n in by and order[n]<order[row['module']]
 qualified.update(q)
q=deque(['Natural80Endpoint']);seen=set()
while q:
 n=q.popleft()
 if n in seen:continue
 seen.add(n);q.extend(by[n]['bare_imports'])
assert seen==set(by)
qr={r['module']:r for r in inv['qualified_direct_sources']};assert set(qr)==qualified and len(qr)==41
for n,r in qr.items():
 assert r['path']=='Lean/'+n.replace('.','/')+'.lean';files[r['path']]=pin(D/r['path'],r['sha256']).decode()
assert len(files)==225
# Independent comment/string scrubber, restricted to the listed supported syntax.
def scrub(s):
 assert not any(x in s for x in ('r#"','s!"','m!"','f!"','«','»'))
 out=[];i=0;depth=0;quote=False;line=False;escape=False
 while i<len(s):
  ch=s[i]; pair=s[i:i+2]
  if depth:
   if pair=='/-':depth+=1;out.extend('  ');i+=2;continue
   if pair=='-/':depth-=1;out.extend('  ');i+=2;continue
   out.append('\n' if ch=='\n' else ' ');i+=1;continue
  if line:
   out.append('\n' if ch=='\n' else ' ');i+=1
   if ch=='\n':line=False
   continue
  if quote:
   out.append('\n' if ch=='\n' else ' ');i+=1
   if escape:escape=False
   elif ch=='\\':escape=True
   elif ch=='"':quote=False
   continue
  if pair=='/-':depth=1;out.extend('  ');i+=2;continue
  if pair=='--':line=True;out.extend('  ');i+=2;continue
  if ch=='"':quote=True;out.append(' ');i+=1;continue
  out.append(ch);i+=1
 assert depth==0 and not quote
 return ''.join(out)
words=('sorry','admit','axiom','unsafe','native_decide','run_tac','implemented_by','ofReduceBool','trustCompiler','partial','unsafeCast','sorryAx','panic!','unreachable!')
escape=re.compile(r"(?<![A-Za-z0-9_'])(?:"+'|'.join(map(re.escape,words))+r")(?![A-Za-z0-9_'])")
choice=re.compile(r"(?<![A-Za-z0-9_'])Classical\.(?:choose!_eq_iff_right|choose_spec|choose!|choose|choice)(?![A-Za-z0-9_'])")
hits=[];choices=[];prints=0
for path,s in files.items():
 s=scrub(s)
 for regex,dest in [(escape,hits),(choice,choices)]:
  for m in regex.finditer(s):dest.append({'path':path,'line':s.count('\n',0,m.start())+1,'token':m.group()})
 prints+=len(re.findall(r'^\s*#print\s+axioms\b',s,re.M))
sort=lambda x:sorted(x,key=lambda z:(z['path'],z['line'],z['token']))
assert sort(hits)==sort(tok['escape_hits']) and sort(choices)==sort(tok['classical_selection_hits'])
assert len(hits)==15 and all(x['token']=='partial' for x in hits) and len(choices)==5 and prints==314
assert tok['unsupported_files']==[] and tok['checked_source_count']==225
print(json.dumps({'scope':'independent bounded headers, source hashes and supported lexical scrub; no Lean, axiom or provider closure','drafts':len(rows),'reachable':len(seen),'qualified':len(qr),'shared_natural81':len(shared),'new_drafts':11,'partial_hits':len(hits),'classical_selection_hits':len(choices),'unexecuted_axiom_commands':prints},sort_keys=True,indent=2))
