#!/usr/bin/env python3
"""Independent offline recheck of frozen source survey; no Lean execution."""
import hashlib,json,re,sys,os,tomllib
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize: raise SystemExit('requires python3 -I -S -B')
root=next(p for p in Path(__file__).resolve().parents if (p/'lakefile.toml').is_file())
research=root/'Computability/DiophantineConsistency/research'; survey=research/'nine-variable-current-base-source-survey'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={'survey.py':'8889c71de40c550f369cc950b4f90d4d8ed4a3afc45bd44099a1cd54c8e2ebf6','result-final.json':'7aa788ec612ef2d1cf40e65cf16b507099532477cd581dfe2c560d7b934d31ca'}
for name,h in pins.items():
 if sha(survey/name)!=h:raise ValueError(('survey pin',name))
a=json.loads((survey/'result-final.json').read_bytes()); manifest=json.loads((research/'current14-standard-fresh-rebuild-preflight/snapshot-manifest.json').read_bytes()); state=json.loads(Path('/tmp/current14-standard-fresh-build-20261104/state.json').read_bytes())
if sha(research/'current14-standard-fresh-rebuild-preflight/snapshot-manifest.json')!=a['base_manifest_sha256'] or sha(Path('/tmp/current14-standard-fresh-build-20261104/state.json'))!=a['base_state_sha256']: raise ValueError('base pins')
# A separate lexical pass suppresses nested comments, line comments and strings.
def imports(text):
 i=0; state='code'; depth=0; lines=[]; line=''
 while i<len(text):
  c=text[i]; pair=text[i:i+2]
  if state=='line':
   if c=='\n': lines.append(line);line='';state='code'
   i+=1;continue
  if state=='block':
   if pair=='/-': depth+=1;i+=2;continue
   if pair=='-/': depth-=1;i+=2;state='code' if depth==0 else 'block';continue
   if c=='\n':lines.append(line);line=''
   i+=1;continue
  if state=='string':
   if c=='\\': i+=2;continue
   if c=='"':state='code'
   if c=='\n':lines.append(line);line=''
   i+=1;continue
  if pair=='--':state='line';i+=2;continue
  if pair=='/-':state='block';depth=1;line+=' ';i+=2;continue
  if c=='"':state='string';line+=' ';i+=1;continue
  if c=='\n':lines.append(line);line=''
  else:line+=c
  i+=1
 if state in ('block','string'): raise ValueError('unterminated source literal/comment')
 lines.append(line);out=[]
 for line in lines:
  m=re.match(r'^\s*(?:public\s+)?import\s+(.+)$',line)
  if m:
   words=m.group(1).split()
   if any(not re.fullmatch(r'[\w.]+',w) for w in words):raise ValueError(('unsupported',line))
   out.extend(words)
 return out
sources=a['project_sources']; base=manifest['sources']; shared=set(sources)&set(base); ext=set(sources)-set(base)
lake=tomllib.loads((root/'lakefile.toml').read_text()); libs={x['name']:root/x.get('srcDir','.') for x in lake['lean_lib'] if x['name']!='Foundation'}
def local_path(mod):
 for n in sorted(libs,key=len,reverse=True):
  if mod==n or mod.startswith(n+'.'):return libs[n]/('/'.join(mod.split('.'))+'.lean')
 return None
if (len(sources),len(shared),len(ext))!=(1212,995,217):raise ValueError('counts')
for mod,rec in sources.items():
 f=root/rec['source']; text=f.read_text()
 if local_path(mod)!=f:raise ValueError(('project root mapping',mod))
 if sha(f)!=rec['source_sha256'] or imports(text)!=rec['imports']:raise ValueError(('source/import',mod))
 if mod in shared and (base[mod]['sha256']!=rec['source_sha256'] or base[mod]['imports']!=rec['imports']):raise ValueError(('base source',mod))
order=a['extension_order']; pos={n:i for i,n in enumerate(order)}
if len(pos)!=len(order) or set(order)!=ext:raise ValueError('order inventory')
for mod in order:
 for dep in sources[mod]['imports']:
  if dep in ext and pos[dep]>=pos[mod]: raise ValueError(('order edge',mod,dep))
seen=set();external=set();todo=list(a['targets'])
while todo:
 m=todo.pop()
 if m not in sources:external.add(m);continue
 if m not in seen:seen.add(m);todo.extend(sources[m]['imports'])
if seen!=set(sources) or external!=set(a['declared_external']):raise ValueError('closure or external mismatch')
if any(local_path(m) is not None for m in external):raise ValueError('project dependency classified as external')
records={r['module']:r for r in state['records']}; paths={}; edges=0
for name in shared:
 rec=records[name]
 if rec['exit']!=0 or set(rec['direct_inputs'])-{'Init'}!=set(sources[name]['imports'])-{'Init'}:raise ValueError(('base direct',name))
 for f,e in state['outputs'][name].items():
  x=Path(f)
  if e is None:
   if os.path.lexists(x):raise ValueError(('unexpected companion',f))
  elif not x.is_file() or str(x.resolve())!=e['realpath'] or sha(x)!=e['sha256']:raise ValueError(('output',f))
 for dep,e in rec['direct_inputs'].items():
  x=Path(e['path']); edges+=1
  if str(x) in paths and paths[str(x)]!=e['sha256']:raise ValueError(('inconsistent input',str(x)))
  if str(x) not in paths:
   if not x.is_file() or sha(x)!=e['sha256']:raise ValueError(('input',str(x)))
   paths[str(x)]=e['sha256']
if edges!=4163 or len(paths)!=1096:raise ValueError('base input counts')
for mod, choices in a['external_provider_candidates'].items():
 rel=Path(*mod.split('.')).with_suffix('.olean')
 roots=(Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'))
 actual=[str(parent/rel) for parent in roots if (parent/rel).is_file()]
 if actual!=[c['path'] for c in choices]:raise ValueError(('candidate inventory',mod))
 for c in choices:
  p=Path(c['path'])
  if not p.is_file() or str(p.resolve())!=c['realpath'] or sha(p)!=c['sha256']:raise ValueError(('external candidate drift',mod))
if a['missing_external'] or a['different_hash_multiple_provider_candidates']:raise ValueError('retained candidate list is not clean')
print(json.dumps({'status':'PASS_SOURCE_SURVEY_REVIEW','sources':len(sources),'shared':len(shared),'extension':len(ext),'direct_edges':edges,'direct_paths':len(paths),'external_names':len(external),'lakefile_sha256_point_in_time':sha(root/'lakefile.toml'),'scope':'Independent parser and recorded artifact rehash, not Lean, provider selection or package-transitive audit.'},sort_keys=True,indent=2))
