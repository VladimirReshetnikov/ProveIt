#!/usr/bin/env python3
"""Fail-closed source-declared survey only; never invokes Lean or builds."""
import contextlib,hashlib,io,json,os,runpy,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent;root=next(x for x in here.parents if (x/'lakefile.toml').is_file()); research=here.parent
scanpath=research/'nine-variable-ipra/bounded-build-preflight/scan.py';manifest=research/'current14-standard-fresh-rebuild-preflight/snapshot-manifest.json';obs=research/'current14-standard-fresh-rebuild-preflight/run-observation.json';state=Path('/tmp/current14-standard-fresh-build-20261104/state.json')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def need(b,msg):
 if not b:raise RuntimeError(msg)
pins={root/'lakefile.toml':'a378413000dd01d021315457d6c569202cca123f99dd224774e951fef3ec9b4f',scanpath:'d72f3242ff991ad537217b8b25c3cde4ab091a06ce45f61d4f92f70886848816',manifest:'1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749',obs:'5d45638261f749227f6530b55154b7d3c28197e1e04ab0eaffb10876e2fa3475',state:'f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014'}
initial_self=sha(Path(__file__))
def check_pins():
 for f,h in pins.items():need(f.is_file() and sha(f)==h,'pinned input mismatch '+str(f))
 need(sha(Path(__file__))==initial_self,'preflight source changed')
check_pins();m=json.loads(manifest.read_bytes());b=json.loads(state.read_bytes());ob=json.loads(obs.read_bytes())
need(b['status']=='PASS' and b['source_status']=='CURRENT_AT_FINAL_CHECK' and b['manifest_sha256']==pins[manifest] and ob['exit']==0 and ob['build_status']=='PASS','base status')
with contextlib.redirect_stdout(io.StringIO()):s=runpy.run_path(str(scanpath))
targets=['DiophantineConsistency.ModelCarrierScaled','DiophantineConsistency.ModelCarrierSyntax','DiophantineConsistency.ModelArithmetic','DiophantineConsistency.IPRAExpressionNative','DiophantineConsistency.HACurrentEquation2011']
all={};external=set();missing={}
for t in targets:
 seen,absent,ext=s['graph'](t);missing.update(absent);external.update(ext)
 for name,rec in seen.items():
  need(name not in all or all[name]==rec,'source mismatch between traversals '+name);all[name]=rec
need(not missing,'missing source '+repr(missing));shared=sorted(set(all)&set(m['sources']));extra=set(all)-set(m['sources'])
need((len(all),len(shared),len(extra))==(1007,991,16),'unexpected source closure count')
for name in shared:
 need(all[name]['source_sha256']==m['sources'][name]['sha256'] and all[name]['imports']==m['sources'][name]['imports'],'base source/import drift '+name)
records={x['module']:x for x in b['records']};base_root=Path('/tmp/current14-standard-fresh-build-20261104/lib');suffixes=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def base_check():
 seen={};edges=0; outputs=0
 for name in shared:
  need(name in records and name in b['outputs'],'missing base producer '+name);rec=records[name]
  need(rec['exit']==0 and rec['source_sha256']==all[name]['source_sha256'],'base record mismatch '+name)
  stem=base_root.joinpath(*name.split('.'));expected={str(stem)+x for x in suffixes};out=b['outputs'][name]
  need(set(out)==expected,'base output inventory mismatch '+name)
  main=out[str(stem)+'.olean'];need(main is not None and main['sha256']==rec['object_sha256'],'base main object link '+name)
  for raw,v in out.items():
   f=Path(raw);outputs+=1
   if v is None:need(not os.path.lexists(f),'unexpected base companion '+raw)
   else:need(f.is_file() and str(f.resolve())==v['realpath'] and sha(f)==v['sha256'],'base output mismatch '+raw)
  deps=rec['direct_inputs'];need(set(deps)-{'Init'}==set(all[name]['imports'])-{'Init'},'base direct names mismatch '+name)
  for dep,v in deps.items():
   f=Path(v['path']);edges+=1
   need(str(f) not in seen or seen[str(f)]==v['sha256'],'conflicting direct input '+str(f))
   if str(f) not in seen:need(f.is_file() and sha(f)==v['sha256'],'base direct drift '+str(f));seen[str(f)]=v['sha256']
 return {'checked_outputs_and_absences':outputs,'checked_direct_edges':edges,'distinct_direct_paths':len(seen)}
active=set();done=set();order=[]
def visit(n):
 if n in done:return
 need(n not in active,'source cycle '+n);active.add(n)
 for dep in all[n]['imports']:
  if dep in all:visit(dep)
 active.remove(n);done.add(n)
 if n in extra:order.append(n)
for t in targets:visit(t)
need(len(order)==16 and set(order)==extra,'incomplete extension order');pos={n:i for i,n in enumerate(order)}
for n in order:
 for dep in all[n]['imports']:
  if dep in extra:need(pos[dep]<pos[n],'invalid extension ordering '+n)
new_external=sorted(external-set(m['external_modules']))
expected_extra=['Mathlib.Algebra.MvPolynomial.CommRing','Mathlib.Algebra.Order.Ring.Abs','Mathlib.Algebra.Order.Ring.Cone','Mathlib.Data.Int.Basic','Mathlib.Data.Int.Order.Units']
need(new_external==expected_extra,'unexpected external additions')
roots=[base_root,Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
need(not any(not x.is_dir() for x in roots),'missing candidate provider root')
def candidates():
 out={}
 for n in sorted(external|{'Init'}):
  entries=[];stem=Path(*n.split('.'))
  for root0 in roots:
   parts={}
   for suffix in suffixes:
    f=root0/(str(stem)+suffix)
    if os.path.lexists(f):need(f.is_file(),'broken candidate '+str(f));parts[suffix]={'path':str(f),'realpath':str(f.resolve()),'sha256':sha(f)}
    else:parts[suffix]=None
   entries.append(parts)
  available=[parts['.olean'] for parts in entries if parts['.olean'] is not None]
  need(available,'missing external main object '+n)
  need(len({x['sha256'] for x in available})==1,'different external main candidates '+n)
  out[n]=entries
 return out
before=base_check();cs=candidates()
for n,rec in all.items():need(sha(root/rec['source'])==rec['source_sha256'],'source drift '+n)
need(candidates()==cs,'external candidates changed during preflight');need(base_check()==before,'base observations changed');check_pins()
result={'status':'PASS_SOURCE_DECLARED_PREFLIGHT_NOT_BUILD_AUTHORIZATION','targets':targets,'project_count':len(all),'shared_base_count':len(shared),'extension_count':len(order),'extension_order':order,'project_sources':dict(sorted(all.items())),'base_checks':before,'declared_external':sorted(external),'new_declared_external':new_external,'candidate_provider_roots':[str(x) for x in roots],'external_candidates':cs,'pins':{str(k):v for k,v in pins.items()},'preflight_sha256':initial_self,'scope':'Current source-declared closure and point-in-time artifact candidates. No Lean deps, immutable source snapshot, dynamic ancestry, complete transitive compatibility, or build authorization.'}
print(json.dumps(result,sort_keys=True,indent=2))
