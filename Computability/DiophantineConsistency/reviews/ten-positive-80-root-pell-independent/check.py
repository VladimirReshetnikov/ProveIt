#!/usr/bin/env python3
"""Audit the exact 80-row graph, root and Pell author receipts without Lean."""
from hashlib import sha256
import json,os,re,subprocess,sys
from pathlib import Path
if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];G=D/'research/ten-positive-80-model-binding-prototype';P=D/'research/ten-positive-80-pell-prototype'
DATA=D/'research/ten-positive-unshift-t-finite/data/equation_qcube_V2.json';J=D/'research/ordinary12-direct90-ipra-join/observations/attempt03/result.json'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PINS={DATA:'fcc5e40f5d22320541ec2af5857725ceafaa69d0df36708ec60d6b9a40a71f01',
 J:'09430817390268544ed668c691d9aaf335c68b85386c2acb6a3d7b1d76f239ed',
 G/'Direct80Graph.lean':'f7214574d3c3266b358abf493b3c0c4ab00721a496afb0866f072165b8b93380',
 G/'Direct80Root.lean':'a3f2ec17d61bc4720d2bff647e091c5b5346438b309a1ec647eeeefae47b0ac9',
 G/'Direct80Factors.lean':'f2dfa54370d5bed6bb9253b5a722369222c5550ddf4af4c2ec8a4631c7b1e524',
 P/'Direct80Pell.lean':'2cba59b067dccb9f7710d9dc54d67628ecee8ad29e3268b294f357b295dd93c3',
 G/'observations/attempt04/terminal.json':'5c8b5c7d96c2ca19d9712bc5ecdb7744d854bd30d9033e198e2e01d6b02371ab',
 G/'observations/root-attempt06/terminal.json':'429ce1b54c6ce1a5fa78416bfa2b5d4554883087c8837acd5413308ea8ad6392',
 G/'observations/factors-attempt04/terminal.json':'8f1760b431b2818c056c94a39146c729c50365ac66d4ad0f10eec2ad51d37856',
 P/'observations/pell-attempt02/terminal.json':'1102da145f79115e74e35be5b3038b1604e0291c52571bcbc7c916d0a729d6c5',
 LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
for name,digest in {
 'attempt01':'8932d173c183e76484bb87699572b06572897b86b0d4c5396f637d1ad5b14d4c',
 'attempt02':'0c03fd182e703b9e42981914bbc175b1625e77e1f8fdc95cdd00358d9fcbce92',
 'attempt03':'50550449f9f5ba7e2448fc86e8f04fb11ea9818a0be2a115b03ae7de759626f8',
 'root-attempt01':'324be139cc7f09766c29e3bc6578337e7aef2f6d64d048e54e6e456a959cc83d',
 'root-attempt02':'416ec2384b23fb0726209cc96778cd82d734025dd3798bcafbb07026022abfeb',
 'root-attempt03':'00a12684b2611c2a3a0c9c37604bc618272b14905a6e859d2e8855fb8f343996',
 'root-attempt04':'62c9b04d20ce78b1cf366e261ae6901d6b3c1c8504a153dae34039d225755050',
 'root-attempt05':'731cb44c4904cf20123834e393747c6977464f5681fb9b131136a6adb67a1c5e',
 'factors-attempt01':'3acf542ea4d502b4475d58c6cc872641112a76f7ab0bbb2f78d465c704a666c0',
 'factors-attempt02':'c88827a6329af81880e76ae3fe6d05fcce88985c47b71007d2cb08735901d1ae',
 'factors-attempt03':'2179ca370f4d502b13930a2821d1adf861ba46bd8c7e2431d4f8ff7e37eeb675'}.items():
 PINS[G/'observations'/name/'terminal.json']=digest
PINS[P/'observations/pell-attempt01/terminal.json']='25c0391675cbfaa8b20b4f50c4563093893ffca1261396fe2765f319b295aa98'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
def rec(p):
 p=Path(p)
 if not os.path.lexists(p):return None
 need(p.is_file(),'non-file '+str(p));return {'sha256':sha(p),'resolved':str(p.resolve(strict=True)),'link':os.readlink(p) if p.is_symlink() else None}
for p,h in PINS.items():need(sha(p)==h,'pin drift '+str(p))
graph=json.loads(DATA.read_text());source=(G/'Direct80Graph.lean').read_text();body=source.split('def graph (p : Fin 4 → ℤ) : Graph :=',1)[1].split('\ntheorem a_shape',1)[0];lines=body.strip().splitlines()
expect=[f'let {n} : Expr (Fin 10) := .var {i}' for i,n in enumerate(graph['witnesses'])]+[f'let {n} : Expr (Fin 10) := .constant (p {i})' for i,n in enumerate(graph['fixed_numerals'])]
need(len(graph['witnesses'])==10 and len(graph['fixed_numerals'])==4 and [x.strip() for x in lines[:14]]==expect,'variable/port slots')
parsed=[]
for line in lines[14:-1]:
 match=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line);need(match is not None,'unparsed row '+line)
 n,x,op,y=match.groups();parsed.append([n,op,int(x) if x.isdigit() else x,int(y) if y.isdigit() else y])
def rename(x):return 'fourAm1' if x=='4Am1' else x
need(parsed==[[rename(n),op,rename(x),rename(y)] for n,op,x,y in graph['source']],'Lean/JSON rows')
need(lines[-1].strip()=='⟨Delta,U,Dtau,DpI2,Dg,Q,V,Znum,Mtot,N⟩' and graph['output']=='N','field binding')
known=set(graph['witnesses']+graph['fixed_numerals'])|{0,1,2,3,4};parents={}
for n,op,x,y in graph['source']:
 need(n not in known and x in known and y in known and op in ('+','-','*'),'graph topology');parents[n]=(x,y);known.add(n)
live=set();todo=['N']
while todo:
 n=todo.pop()
 if n in parents and n not in live:live.add(n);todo.extend(parents[n])
need(len(parsed)==len(live)==80,'live rows')
author=subprocess.run([sys.executable,'-I','-S','-B',str(G/'check-graph.py')],capture_output=True,timeout=30)
need(author.returncode==0 and not author.stderr and author.stdout==(G/'observations/graph-comparison01/stdout').read_bytes(),'captured external comparison')
accepted=[(G,'attempt04','Direct80Graph','run.py','95eb93d8d48d28df810997b666e061ff20aab90e0adbf357e7590c511d2465d4'),
 (G,'root-attempt06','Direct80Root','run-root.py','6cb873420b53fcfa692f16c59d35941a4c56f78f70ab26a3684e33adaa2509c0'),
 (G,'factors-attempt04','Direct80Factors','run-factors.py','3703cad8beb421022aba3a80849f71c90b77d603e4567164652d72f2e8f954a0'),
 (P,'pell-attempt02','Direct80Pell','run.py','764c9ce5f5f8e55323128ef195307ca030eee2596bd6eda283a6e0fc2be97807')]
old=json.loads(J.read_text());need(old['status']=='PASS','prior 90 join');direct={};samples=0
for root,name,module,runner,objhash in accepted:
 obs=root/'observations'/name;d=json.loads((obs/'terminal.json').read_text());pins=d['pins'];need(d['exit']==0 and d['reason'] is None and pins==d['after'],'accepted stage '+name)
 need(sha(root/(module+'.lean'))==sha(obs/'source.txt')==pins['source']==PINS[root/(module+'.lean')],'source snapshot '+name)
 need(sha(root/runner)==pins['runner'] and sha(LEAN)==pins['lean'],'runner/tool '+name)
 provider=Path('/tmp/direct90-ipra-join-b66u_qqo/lib/DiophantineConsistency')/('WeightedExpressionDegree.olean' if module=='Direct80Graph' else 'ArithmeticGcdNormalization.olean')
 need(sha(provider)==pins['direct_provider'],'direct provider pin '+name)
 obj=Path(d['output_root'])/(module+'.olean');need(sha(obj)==d['object_sha256']==objhash,'object '+name)
 need(sha(obs/'stdout')==d['stdout_sha256'] and sha(obs/'stderr')==d['stderr_sha256'] and not (obs/'stderr').read_bytes(),'logs '+name)
 stdout=(obs/'stdout').read_text();need(not re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',stdout) and 'sorryAx' not in stdout,'diagnostic '+name)
 reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",stdout,re.M)
 need(reports and all(set(x.strip() for x in a.split(','))<={'propext','Classical.choice','Quot.sound'} for _,a in reports),'axioms '+name)
 pre=d['preflight'];need(pre['mem_available_kib']>=8*1024**2 and len(pre['lean'])<2,'resource preflight')
 for sample in d['samples']:
  need(sample['mem_available_kib']>=8*1024**2 and len(sample['lean'])<=2,'resource sample');samples+=1
 roots=[Path(x) for x in d['lean_path'].split(':')]
 for n in re.findall(r'^import\s+(\S+)',(root/(module+'.lean')).read_text(),re.M):
  rel=Path(n.replace('.','/')+'.olean')
  selected=next((r/rel for r in roots if (r/rel).is_file()),None);need(selected is not None,'unresolved direct import '+n)
  if '.' in n:
   first_namespace=next((r for r in roots if (r/n.split('.')[0]).is_dir()),None)
   need(first_namespace is not None and (first_namespace/rel).is_file(),'namespace shadow '+n)
  record={'path':str(selected),'sha256':sha(selected)};direct[n]=record
  oldrow=old['post_headers']['project'].get(n)
  if oldrow is not None:
   need(record['sha256']==oldrow['record']['sha256'],'90 selected import mismatch '+n)
   stem=str(selected)[:-len('.olean')]
   for suffix,entry in oldrow['companions'].items():
    now=rec(stem+suffix)
    need((None if now is None else now['sha256'])==(None if entry is None else entry['sha256']),'90 companion mismatch '+n+suffix)
# Extra prototype objects were directly pinned by the later runners.
extra=['/tmp/tenpositive-80factors-wjl9x3rl/Direct80Factors.olean','/tmp/tenpositive-80root-vb74zjn5/Direct80Root.olean',
 '/tmp/tenpositive-80graph-d2v79zbc/Direct80Graph.olean','/tmp/tenpositive-product-root-kdq8sqms/ProductRoot.olean',
 '/tmp/tenpositive-doubling-z_t6ngdp/TenPositiveDoubling.olean','/tmp/tenpositive-scaledsquare-rat00ki8/ScaledSquare.olean']
pell=json.loads((P/'observations/pell-attempt02/terminal.json').read_text())
need([sha(x) for x in extra]==pell['pins']['extra'],'Pell predecessor objects')
need(json.loads((G/'observations/root-attempt06/terminal.json').read_text())['pins']['extra']==[sha(x) for x in extra[2:]],'root predecessors')
need(json.loads((G/'observations/factors-attempt04/terminal.json').read_text())['pins']['extra']==[sha(x) for x in extra[1:]],'factor predecessors')
# Preserve distinctions between true failures, earlier smaller versions, and
# warning-rejected runs: a zero compiler exit is not automatically acceptance.
cases={'attempt01':(1,'error'),'attempt02':(0,'partial'),'attempt03':(0,'warning'),
 'root-attempt01':(1,'error'),'root-attempt02':(0,'partial'),'root-attempt03':(0,'partial'),
 'root-attempt04':(1,'error'),'root-attempt05':(1,'error'),
 'factors-attempt01':(1,'error'),'factors-attempt02':(0,'partial'),'factors-attempt03':(0,'warning')}
for name,(exitcode,kind) in cases.items():
 obs=G/'observations'/name;d=json.loads((obs/'terminal.json').read_text());log=(obs/'stdout').read_text()+(obs/'stderr').read_text()
 need(d['exit']==exitcode and sha(obs/'source.txt')==d['pins']['source'] and sha(obs/'stdout')==d['stdout_sha256'] and sha(obs/'stderr')==d['stderr_sha256'],'prior attempt '+name)
 if kind=='error':need('error' in log,'missing failure diagnostic '+name)
 if kind=='warning':need('warning:' in log,'missing warning '+name)
obs=P/'observations/pell-attempt01';r=json.loads((obs/'terminal.json').read_text());need(r['exit']==1 and sha(obs/'source.txt')==r['pins']['source'] and sha(obs/'stdout')==r['stdout_sha256'] and 'error' in (obs/'stdout').read_text(),'failed Pell attempt')
factors=(G/'Direct80Factors.lean').read_text();pellsource=(P/'Direct80Pell.lean').read_text()
need('theorem graph_roots' in factors and '(hb : 0<(p 0:V)) (hv : ∀j,0<v j)' in factors and 'InternalZero (graph (integerPorts p)).output v' in factors,'model root assumptions')
need(all(t in factors for t in ('∃ tau f : V, 0<tau ∧ 0<f ∧ E p v=tau*tau',
 '1+delta p v*U p v*U p v*E p v=f*f')),'root conclusion')
need(all(t in pellsource for t in ('∃ tau f n I : V, 0<tau ∧ 0<f ∧ 0<n ∧ n≤K',
 'E0=tau*tau ∧ 1+aa=f*f','xcoord n (2*(P-1)+1)=tau',
 '2*ycoord n (2*(P-1)+1)=K','I=2*U0*tau*f','C*C∣I',
 'D*(4*aa*(1+aa))=(D*I)*(D*I)','positive_parameter_solution P tau K hP hnorm')),'Pell conclusion')
for n,row in direct.items():need(sha(row['path'])==row['sha256'],'direct input changed '+n)
for p,h in PINS.items():need(sha(p)==h,'pin changed during audit '+str(p))
print(json.dumps({'status':'PASS','graph_rows':len(parsed),'live_rows':len(live),'direct_imports':direct,
 'accepted_modules':[x[2] for x in accepted],'prior_model_attempts':len(cases),'failed_pell_attempt':True,
 'resource_samples':samples,'scope':'external source/JSON, author receipts and point-in-time direct imports; no Lean replay, fixed-port halt or iPRA theorem'},indent=2,sort_keys=True))
