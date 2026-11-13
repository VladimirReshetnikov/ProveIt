#!/usr/bin/env python3
"""Independently inspect source closure and point-in-time artifacts; no Lean."""
import hashlib
import json
import os
import re
import tomllib
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if (p/'lakefile.toml').is_file())
RESEARCH=HERE.parents[1]/'research'
PREF=RESEARCH/'normalized106-current14-sixteen-source-preflight'
MAN=RESEARCH/'current14-standard-fresh-rebuild-preflight/snapshot-manifest.json'
STATE=Path('/tmp/current14-standard-fresh-build-20261104/state.json')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,m):
 if not v:raise ValueError(m)
for p,h in [(PREF/'preflight.py','6a9e06d558e0ffa7167fa57460863df0c812e6cf132b1469f8ae6325983697d7'),
 (PREF/'result.json','f159489a58b1804d327a35b98ae75e64d746efe4605de0ce8a25ef3d92ca70b2'),
 (MAN,'1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749'),
 (STATE,'f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014'),
 (ROOT/'lakefile.toml','a378413000dd01d021315457d6c569202cca123f99dd224774e951fef3ec9b4f')]:
 need(sha(p)==h,'pin '+str(p))
r=json.loads((PREF/'result.json').read_bytes());m=json.loads(MAN.read_bytes());b=json.loads(STATE.read_bytes())
term=json.loads((PREF/'terminal-observation.json').read_bytes())
need(term['observed_exit_code']==0 and term['preflight_sha256']==sha(PREF/'preflight.py') and term['result_sha256']==sha(PREF/'result.json'),'terminal record')
libs={x['name']:ROOT/x.get('srcDir','.') for x in tomllib.loads((ROOT/'lakefile.toml').read_text())['lean_lib'] if x['name']!='Foundation'}
def path_for(n):
 matches=[k for k in libs if n==k or n.startswith(k+'.')]
 return libs[max(matches,key=len)].joinpath(*n.split('.')).with_suffix('.lean') if matches else None
def imports(text):
 # Preserve line boundaries while removing nested comments and strings.
 out=[];i=0;depth=0;string=False
 while i<len(text):
  two=text[i:i+2];c=text[i]
  if depth:
   if two=='/-':depth+=1;i+=2;continue
   if two=='-/':depth-=1;i+=2;continue
   out.append('\n' if c=='\n' else ' ');i+=1;continue
  if string:
   if c=='\\':out.extend('  ');i+=2;continue
   if c=='"':string=False
   out.append('\n' if c=='\n' else ' ');i+=1;continue
  if two=='/-':depth=1;out.extend('  ');i+=2;continue
  if two=='--':
   j=text.find('\n',i)
   if j<0:break
   out.extend(' '*(j-i));i=j;continue
  if c=='"':string=True;out.append(' ');i+=1;continue
  out.append(c);i+=1
 need(not depth and not string,'unclosed source comment/string')
 found=[]
 for line in ''.join(out).splitlines():
  match=re.match(r'^\s*(?:public\s+)?import\s+(.+)$',line)
  if match:found.extend(match.group(1).split())
 need(all(re.fullmatch(r'[\w.]+',x) for x in found),'unsupported import')
 return found
sources=r['project_sources'];targets=r['targets'];todo=list(targets);visited=set();external=set()
while todo:
 n=todo.pop()
 if n in visited or n in external:continue
 p=path_for(n)
 if p is None:external.add(n);continue
 need(n in sources and p.is_file(),'missing source '+n)
 rec=sources[n];need(str(p.relative_to(ROOT))==rec['source'] and sha(p)==rec['source_sha256'],'source identity '+n)
 found=imports(p.read_text());need(found==rec['imports'],'source imports '+n)
 visited.add(n);todo.extend(found)
need(visited==set(sources) and external==set(r['declared_external']),'closure')
shared=visited & set(m['sources']);extra=visited-set(m['sources']);order=r['extension_order']
need((len(visited),len(shared),len(extra))==(1007,991,16) and set(order)==extra and len(order)==16,'closure counts')
pos={n:i for i,n in enumerate(order)}
for n in order:
 for dep in sources[n]['imports']:
  if dep in extra:need(pos[dep]<pos[n],'bad extension order')
for n in shared:
 need(sources[n]['source_sha256']==m['sources'][n]['sha256'] and sources[n]['imports']==m['sources'][n]['imports'],'manifest drift '+n)
need(sorted(external-set(m['external_modules']))==r['new_declared_external'] and len(r['new_declared_external'])==5,'external additions')
records={x['module']:x for x in b['records']};seen={};edges=0;outputs=0
suffixes=['.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash']
base=Path('/tmp/current14-standard-fresh-build-20261104/lib')
for n in shared:
 rec=records[n];need(rec['exit']==0 and rec['source_sha256']==sources[n]['source_sha256'],'base record '+n)
 stem=base/n.replace('.','/')
 need(set(b['outputs'][n])=={str(stem)+s for s in suffixes},'base output paths '+n)
 need(b['outputs'][n][str(stem)+'.olean']['sha256']==rec['object_sha256'],'base producer object '+n)
 need(set(rec['direct_inputs'])-{'Init'}==set(sources[n]['imports'])-{'Init'},'direct names '+n)
 for raw,v in b['outputs'][n].items():
  p=Path(raw);outputs+=1
  if v is None:need(not os.path.lexists(p),'unexpected output '+raw)
  else:need(p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],'output '+raw)
 for dep,v in rec['direct_inputs'].items():
  p=Path(v['path']);edges+=1
  if str(p) not in seen:seen[str(p)]=sha(p)
  need(seen[str(p)]==v['sha256'],'direct input '+str(p))
need((outputs,edges,len(seen))==(9910,4151,1093),'base counts')
need(set(r['external_candidates'])==external|{'Init'},'external candidate names')
for name,roots in r['external_candidates'].items():
 main=[]
 for entries in roots:
  for suffix,item in entries.items():
   # Null paths are checked from their known root and module below.
   if item is None:continue
   p=Path(item['path']);need(p.is_file() and str(p.resolve())==item['realpath'] and sha(p)==item['sha256'],'external '+str(p))
  if entries['.olean'] is not None:main.append(entries['.olean']['sha256'])
 need(main and len(set(main))==1,'external candidate collision '+name)
for name,roots in r['external_candidates'].items():
 for root,entries in zip(r['candidate_provider_roots'],roots):
  for suffix,item in entries.items():
   p=Path(root)/(name.replace('.','/')+suffix)
   need((item is None and not os.path.lexists(p)) or (item is not None and str(p)==item['path']),'external absent/path '+str(p))
print(json.dumps({'status':'PASS_POINT_IN_TIME_SOURCE_PREFLIGHT_REVIEW','project':len(visited),'shared':len(shared),'extension':len(extra),'base_outputs':outputs,'direct_edges':edges,'direct_paths':len(seen),'external_names':len(external),'scope':'source-declared graph and current artifacts; no Lean or package transitive ancestry'},sort_keys=True))
