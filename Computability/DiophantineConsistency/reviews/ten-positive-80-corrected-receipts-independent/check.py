#!/usr/bin/env python3
"""Independent read-only audit of five author self-pinned rechecks."""
import ast,json,re,sys
from pathlib import Path
from hashlib import sha256
if sys.flags.optimize:raise RuntimeError('optimized Python')
D=Path(__file__).resolve().parents[2];B=D/'research/ten-positive-80-scaled-growth-prototype';L=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
h=lambda p:sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
E=[('graph','Direct80GraphGrowth','attempt01','attempt02','7645ae1b14ae14ee50dc35d9b348a36cbfbe8a1bedcc0fce53ea6f86bbc91174'),('graphindex','Direct80GraphIndex','graphindex-attempt01','graphindex-attempt02','7786c75ed00f3d8858c715ed5eeffe8b34f41a97f1554f43740ee33b980340da'),('cabovex','Direct80CAboveX','cabovex-attempt01','cabovex-attempt02','9e686df27e81dcd0959a85699badab60a6546612c8e3743d0df041fcb24737f3'),('kpos','Direct80Kpos','kpos-attempt01','kpos-attempt02','0dc99f59ace4d95084e16f1ad98c77fec9869dee447b7e9ccf6631144f266b71'),('size','Direct80Size','size-attempt02','size-attempt03','518f4241992a12e83cd61d83065221d7738e2cffa51e22249edbb0fbb3ff7c64')]
out={};sample_count=0
for name,module,old,new,tpin in E:
 obs=B/'observations'/new;t=obs/'terminal.json';o=B/'observations'/old;need(h(t)==tpin,'terminal pin '+module);j=json.loads(t.read_text());prev=json.loads((o/'terminal.json').read_text());p=j['pins'];src=B/(module+'.lean');run=B/('run-'+name+'-v2.py');runold=B/('run-'+name+'.py')
 need(j['exit']==0 and j['reason'] is None and p==j['after'],'status '+module)
 need(p['runner']==h(run) and p['runner']!=h(B/'run.py') and h(L)==p['lean'],'runner/lean '+module)
 rs=run.read_text();oldrs=runold.read_text();need(rs.count("'runner':sha(Path(__file__))")==2 and oldrs.count("'runner':sha(H/'run.py')")==2,'self pin '+module)
 need(p['source']==h(src)==h(obs/'source.txt')==prev['pins']['source']==h(o/'source.txt'),'source '+module)
 obj=Path(j['output_root'])/(module+'.olean');oldobj=Path(prev['output_root'])/(module+'.olean');need(h(obj)==j['object_sha256']==prev['object_sha256']==h(oldobj),'identical objects '+module)
 need(h(obs/'stdout')==j['stdout_sha256'] and h(obs/'stderr')==j['stderr_sha256'] and not (obs/'stderr').read_bytes(),'logs '+module)
 text=(obs/'stdout').read_text();need(not re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',text) and 'sorryAx' not in text,'diagnostics '+module)
 ax=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",text,re.M);need(ax and all(set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'} for _,a in ax),'axioms '+module)
 provider=Path('/tmp/direct90-ipra-join-b66u_qqo/lib/DiophantineConsistency/ArithmeticGcdNormalization.olean');need(h(provider)==p['direct_provider'],'inherited provider '+module)
 tree=ast.parse(rs);assign=next(n for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='extra' for x in n.targets));extras=[Path(ast.literal_eval(x.args[0])) for x in assign.value.elts]
 for n in tree.body:
  if isinstance(n,ast.AugAssign) and isinstance(n.target,ast.Name) and n.target.id=='extra':extras.extend(Path(ast.literal_eval(x.args[0])) for x in n.value.elts)
  if isinstance(n,ast.Expr) and isinstance(n.value,ast.Call) and isinstance(n.value.func,ast.Attribute) and isinstance(n.value.func.value,ast.Name) and n.value.func.value.id=='extra' and n.value.func.attr=='append':extras.append(Path(ast.literal_eval(n.value.args[0].args[0])))
 need([h(x) for x in extras]==p['extra'],'extra pins '+module)
 roots=[Path(x) for x in j['lean_path'].split(':')];resolved={}
 for imp in re.findall(r'^import\s+(\S+)',src.read_text(),re.M):
  rel=Path(imp.replace('.','/')+'.olean');selected=next((r/rel for r in roots if (r/rel).is_file()),None);need(selected is not None,'missing import '+imp)
  if '.' in imp:
   ns=next((r for r in roots if (r/imp.split('.')[0]).is_dir()),None);need(ns and (ns/rel).is_file(),'shadow '+imp)
  resolved[imp]={'path':str(selected),'sha256':h(selected)}
 pre=j['preflight'];need(pre['mem_available_kib']>=8*1024**2 and len(pre['lean'])<2,'preflight')
 for x in j['samples']:need(x['mem_available_kib']>=8*1024**2 and len(x['lean'])<=2,'samples');sample_count+=1
 out[module]={'new':new,'old':old,'source':p['source'],'object':j['object_sha256'],'runner':p['runner'],'terminal':tpin,'resolved_direct_imports':resolved,'extra_paths':[str(x) for x in extras]}
newindex='/tmp/tenpositive-80graphindex-vb3yq5ei/Direct80GraphIndex.olean';newabove='/tmp/tenpositive-80cabovex-t_50a0_0/Direct80CAboveX.olean'
need(out['Direct80CAboveX']['resolved_direct_imports']['Direct80GraphIndex']['path']==newindex,'new graphindex resolution')
need(out['Direct80Kpos']['resolved_direct_imports']['Direct80CAboveX']['path']==newabove,'new cabovex resolution')
need(newindex in out['Direct80CAboveX']['extra_paths'] and newindex in out['Direct80Kpos']['extra_paths'] and newabove in out['Direct80Kpos']['extra_paths'],'chain selected pins')
failed=B/'observations/size-attempt01/terminal.json';need(h(failed)=='4c5e5faa5e25dd11d2274dd16a617ffb1dc079e2ac2cf29211d377bd940c1664' and json.loads(failed.read_text())['exit']!=0,'failed size receipt')
print(json.dumps({'status':'PASS','accepted':out,'resource_samples':sample_count,'scope':'author receipts, selected inputs and direct import paths; no Lean replay or full transitive ancestry'},indent=2,sort_keys=True))
