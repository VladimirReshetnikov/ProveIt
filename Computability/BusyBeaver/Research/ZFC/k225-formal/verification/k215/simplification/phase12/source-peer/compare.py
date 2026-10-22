#!/usr/bin/env python3
"""Independent inert archive03 comparison. Never imports supplied code or invokes Lean."""
from pathlib import Path
import ast, hashlib, json, re, subprocess
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
PKG=Path('/tmp/k215-4b16429-review/03/k215-proof-simplification-2026-10-21')
PROP=PKG/'patches/proposed'
OUT=Path('/tmp/k215-phase12-import-peer')
LEAN=Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC')
GEN=Path('Computability/BusyBeaver/Research/ZFC/k225-formal/generate_l2k222.py')
NAMES=['ConstructibleChoice','KQ1ZF','L2Lib222','WFModel','WFModelCore','ZFModels','ZFNative']
sha=lambda b:hashlib.sha256(b).hexdigest()
pins={}
def read(p):
 b=p.read_bytes(); pins[str(p)]={'sha256':sha(b),'bytes':len(b)}; return b.decode()
def strip_comments(s):
 out=[]; i=0; depth=0; quoted=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i): depth+=1; out.extend('  '); i+=2
   elif s.startswith('-/',i): depth-=1; out.extend('  '); i+=2
   else: out.append('\n' if s[i]=='\n' else ' '); i+=1
  elif quoted:
   out.append(s[i])
   if s[i]=='\\' and i+1<len(s): out.append(s[i+1]); i+=2
   else:
    if s[i]=='"': quoted=False
    i+=1
  elif s.startswith('/-',i): depth=1;out.extend('  ');i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i); j=len(s) if j<0 else j;out.extend(' '*(j-i));i=j
  else:
   if s[i]=='"':quoted=True
   out.append(s[i]);i+=1
 assert depth==0 and not quoted
 return ''.join(out)
def tokens(s): return re.findall(r'[^\s]+',strip_comments(s))
def imports(s): return re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',strip_comments(s),re.M)
def decls(s):
 s=strip_comments(s)
 pat=re.compile(r'^(?:(?:private|noncomputable|protected)\s+)*(?:theorem|lemma|def|abbrev|structure|inductive)\s+([\w\u0080-\uffff]+)',re.M)
 starts=list(pat.finditer(s)); d={}
 for k,m in enumerate(starts):
  end=starts[k+1].start() if k+1<len(starts) else len(s)
  block=s[m.start():end]
  block=re.split(r'^end\b',block,flags=re.M)[0].strip()
  assert m[1] not in d
  d[m[1]]=block
 return d
base={n:read(ROOT/LEAN/(n+'.lean')) for n in NAMES if (ROOT/LEAN/(n+'.lean')).exists()}
new={n:read(PROP/LEAN/(n+'.lean')) for n in NAMES}
checks={}
for n in ['ConstructibleChoice','KQ1ZF','L2Lib222']:
 remove=lambda x:re.sub(r'^import[^\n]*\n','',x,flags=re.M)
 assert remove(base[n])==remove(new[n]),n
 checks[n]={'exact_nonimport_bytes':True,'before_imports':imports(base[n]),'after_imports':imports(new[n])}
a=decls(base['WFModel']); c=decls(new['WFModelCore']); w=decls(new['WFModel'])
assert len(a)==15 and len(c)==14 and len(w)==1 and set(c)|set(w)==set(a) and not(set(c)&set(w))
for n,v in (c|w).items(): assert tokens(v)==tokens(a[n]),n
# Exact entire core declaration interval, including whitespace/comments, copied once.
old_core=base['WFModel'].split('abbrev ClosedWF',1)[1].split('/-- The needed closure',1)[0]
new_core=new['WFModelCore'].split('abbrev ClosedWF',1)[1].split('end SetTheory.BusyBeaver.ZFC.WFModel',1)[0]
assert old_core==new_core
checks['WFModel']={'before':list(a),'core':list(c),'wrapper':list(w),'all_declaration_tokens_equal':True,'entire_core_interval_bytes_equal':True,'namespace_unchanged':True,'private_moved':['raw_rel_iff']}
zold=decls(base['ZFNative']); znew=decls(new['ZFNative']); zpure=decls(new['ZFModels'])
assert set(zpure)=={'models_ZF'} and set(zold)==set(znew)|set(zpure) and not set(znew)&set(zpure)
for n,v in (znew|zpure).items():assert tokens(v)==tokens(zold[n]),n
checks['ZFNative']={'before':list(zold),'retained':list(znew),'moved':list(zpure),'all_declaration_tokens_equal':True,'namespace_unchanged':True}
# Parse only literal AST assignments, never execute/import the proposed generator.
gold=read(ROOT/GEN); gnew=read(PROP/GEN)
insertion='    ("import BusyBeaver.ZFC.Enum254", "import BusyBeaver.ZFC.Code254"),\n'
assert gnew==gold.replace('SUBS = [\n','SUBS = [\n'+insertion,1)
def subs(s):
 tree=ast.parse(s)
 return ast.literal_eval(next(n.value for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='SUBS' for t in n.targets)))
assert subs(gnew)==[('import BusyBeaver.ZFC.Enum254','import BusyBeaver.ZFC.Code254')]+subs(gold)
# Only this generated library uses that import among the three input sources.
generator_inputs={}
for f in ['L2Lib254','L2Macros254','L2Control254']:
 s=read(ROOT/LEAN/(f+'.lean'));generator_inputs[f]=imports(s)
assert [f for f,im in generator_inputs.items() if 'BusyBeaver.ZFC.Enum254' in im]==['L2Lib254']
checks['producer']={'exact_single_literal_insertion':True,'insertion':insertion.strip(),'literal_SUBS_delta':subs(gnew)[:1],'source_imports':generator_inputs,'no_execution':True}
# Discover module providers from the live 197 source root inventory, then all sources
# under those distinct roots. This permits compatibility roots outside the primary set.
inv=json.loads(read(Path('/tmp/k215-generic-cd58-check/inline-full-run1/inventory.json')))
roots=set()
for r in inv['modules']:
 p=Path(r['source']); suffix=Path(*r['module'].split('.')).with_suffix('.lean')
 if p.is_relative_to(ROOT) and str(p).endswith(str(suffix)):
  roots.add(Path(str(p)[:-len(str(suffix))]))
assert len(roots)==4,roots
providers={}
for root in sorted(roots):
 for p in sorted(root.rglob('*.lean')):
  if any(part.startswith('.') for part in p.relative_to(root).parts):continue
  m='.'.join(p.relative_to(root).with_suffix('').parts)
  if m.startswith('BusyBeaver.') and not m.startswith('BusyBeaver.ZFC.') and m not in {r['module'] for r in inv['modules']}:continue
  assert m not in providers,(m,p,providers.get(m));providers[m]=p
sources={m:read(p) for m,p in providers.items()}
overlay={'BusyBeaver.ZFC.'+n:new[n] for n in NAMES}
def graph(overrides,targets):
 visiting=set();done=set();order=[];edges={};external=set()
 def visit(m):
  if m in done:return
  if m in visiting:raise AssertionError(('cycle',m))
  if m not in overrides and m not in sources:
   external.add(m);assert m=='Init',m;return
  visiting.add(m); im=imports(overrides.get(m,sources.get(m)));edges[m]=im
  for dep in im:visit(dep)
  visiting.remove(m);done.add(m);order.append(m)
 for m in targets:visit(m)
 return {'count':len(done),'order':order,'imports':edges,'external':sorted(external),'source_bytes':sum(len(overrides.get(m,sources.get(m)).encode()) for m in done)}
scenarios={}
for label,over in [('current',{}),('proposal',overlay)]:
 for targetlabel,targets in [('endpoint',['BusyBeaver.ZFC.KEndpoint215']),('union',['BusyBeaver.ZFC.KEndpoint215','BusyBeaver.ZFC.KDecoderPrefix215']),('legacy',['BusyBeaver.ZFC.WFTheory','BusyBeaver.ZFC.ZFNative'])]:
  scenarios[label+'_'+targetlabel]=graph(over,targets)
assert scenarios['current_endpoint']['count']==192
assert scenarios['current_union']['count']==197
assert scenarios['proposal_endpoint']['count']==179
assert scenarios['proposal_union']['count']==184
for tag in ['endpoint','union','legacy']:
 oldset=set(scenarios['current_'+tag]['order']); newset=set(scenarios['proposal_'+tag]['order'])
 scenarios['proposal_'+tag]['added']=sorted(newset-oldset);scenarios['proposal_'+tag]['removed']=sorted(oldset-newset)
# All public exports of WFModel and ZFNative remain reachable from old module paths.
for rootname in ['WFModel','ZFNative']:
 closure=graph(overlay,['BusyBeaver.ZFC.'+rootname])['order']
 public_before={k:v for k,v in decls(base[rootname]).items() if not v.startswith('private ')}
 found={}
 for m in closure:
  if m in overlay and m in ['BusyBeaver.ZFC.WFModel','BusyBeaver.ZFC.WFModelCore','BusyBeaver.ZFC.ZFNative','BusyBeaver.ZFC.ZFModels']:
   found.update(decls(overlay[m]))
 for n,v in public_before.items():assert n in found and tokens(v)==tokens(found[n])
 checks[rootname]['public_old_import_compatibility']=True
# Only raw_rel_iff is private in the moved interval; no outside references exist.
private_refs=[]
for m,s in sources.items():
 if re.search(r'\braw_rel_iff\b',strip_comments(s)):private_refs.append(m)
assert private_refs==['BusyBeaver.ZFC.WFModel'],private_refs
checks['private_references']={'raw_rel_iff':private_refs}
# Bind current closure to immutable HEAD; compiler objects are not inspected.
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
current=set(scenarios['current_union']['order']);headpins={}
for m in sorted(current):
 p=providers[m];rel=p.relative_to(ROOT)
 b=subprocess.check_output(['git','show',head+':'+str(rel)],cwd=ROOT)
 assert b==sources[m].encode(),('current differs from HEAD',m)
 headpins[m]=sha(b)
# Reread every recorded file, including the delivered proposal, before emitting.
for p,pin in pins.items():assert sha(Path(p).read_bytes())==pin['sha256'],p
result={'status':'PASS_INDEPENDENT_SOURCE_ONLY_REVIEW','head':head,'scope':'Own inert comparison and dependency census only. No supplied producer, verifier, Lean compiler, or proof object executed. This is not elaboration or kernel acceptance.','checks':checks,'scenarios':scenarios,'current_union_head_bindings':headpins,'pins':pins}
(OUT/'comparison.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'head':head,'closures':{k:v['count'] for k,v in scenarios.items()},'endpoint_bytes':{k:scenarios[k+'_endpoint']['source_bytes'] for k in ['current','proposal']},'removed':scenarios['proposal_endpoint']['removed'],'added':scenarios['proposal_endpoint']['added'],'comparison_sha256':sha((OUT/'comparison.json').read_bytes())},indent=2))
