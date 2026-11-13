#!/usr/bin/env python3
"""Read-only independent audit of forward 90-row draft and recorded Lean check."""
from pathlib import Path
from hashlib import sha256
from collections import Counter
import json, os, re, subprocess, sys
if sys.flags.optimize: raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2]; P=D/'research/ordinary12-direct-main-probe'; O=P/'observations/graph-attempt01'; A=P/'observations/dag-attempt01'
parent=D/'research/ordinary12-xq91-candidate/candidate.json'; B=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'
pins={P/'GRAPH.md':'76c951db1500d35a5556386301a2ca3068e5802baccec7985a180ded650b7f8e',P/'graph-dag.json':'82dd1f55f67ef3487509a6d4d31ef085d5d4813c11df43be40570a3293a8b430',P/'DirectMainGraph.lean':'6e465bd6329d4932b3c75e2984f9b771b5ae99d329f946aebba88abaa283c216',P/'run-graph.py':'59e6bef9b30cce402ed7b558373ea30e65fbed7869467249885caaac398beb5f',P/'check-dag.py':'82b4a94e9272c63a8fad01a9ee6a8f16754f5220b51595e22f4e29ddec997258',O/'terminal.json':'6b1d05e8b34b8f5f701ad424b897bb996a9b2e519d08bd451ff1935b0e8e2c68',O/'stdout':'907b5a0886a041f1aacce022d887ecb3a06c45de9db41a2d4c3e8b17c4a13075',A/'terminal.json':'9f980121bd212f3f0cf7453fe8281b5cb396f5781ccb9f88e4814deba8375cbf',A/'stdout':'f11f977afdbdcd5ed75a026b274b7dd5f0810dcd9a4e86a2b5fa5cd213e79399',parent:'fde7510bbc984b7160e92ed5caff260fc90a25c9c24437efbf5c2f40c3f92513',B:'8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f'}
def need(v,m):
 if not v: raise SystemExit(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def checkpins():
 for p,h in pins.items():need(sha(p)==h,'pin mismatch '+str(p))
checkpins(); old=json.loads(parent.read_text());new=json.loads((P/'graph-dag.json').read_text()); source=(P/'DirectMainGraph.lean').read_text(); rec=json.loads((O/'terminal.json').read_text()); dr=json.loads((A/'terminal.json').read_text()); base=json.loads(B.read_text())
need(source.startswith('import XQ91\n'),'direct import changed')
need('variable {R : Type*} [CommRing R]' in source and 'Function.update v 11 (v 11 + v 5)' in source,'ring/update scope mismatch')
for name in ('first','main','ordinary'):
 statement=source.split('theorem '+name+'_eval',1)[1].split(':= by',1)[0]
 need('(p : Fin 4 → ℤ) (v : Fin 12 → R)' in statement and '(graph p).'+name+'.evalRing (liftG v) = (FreeJXQ91.graph p).'+name+'.evalRing v' in statement,'theorem statement mismatch '+name)
need(new['witnesses']==['J','F','alpha','t','T','w','s','r','eta','zeta','n','direct'] and old['witnesses'][-1]=='gamma','witness shape')
need(new['fixed_numerals']==old['fixed_numerals']==['beta','K0','MC','MF'] and new['output']==old['output']=='P12' and new['residuals']==['A0','A1','N'],'interface mismatch')
body=source.split('def graph (p : Fin 4 → ℤ) : Graph :=',1)[1].split('\nvariable {R : Type*}',1)[0]
lines=body.strip().splitlines(); expected_decls=[f'  let {name} : Expr (Fin 12) := .var {i}' for i,name in enumerate(new['witnesses'])]+[f'  let {name} : Expr (Fin 12) := .constant (p {i})' for i,name in enumerate(new['fixed_numerals'])]
need([x.strip() for x in lines[:16]]==[x.strip() for x in expected_decls],'source slots mismatch')
parsed=[]
for line in lines[16:-1]:
 m=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line); need(m is not None,'unparsed source line '+line)
 n,x,op,y=m.groups(); parsed.append([n,op,int(x) if x.isdigit() else x,int(y) if y.isdigit() else y])
need(lines[-1].strip()=='⟨A0, A1, N, P12⟩' and parsed==new['source'],'source-row/output mismatch')
oldrows=old['source']; old_map={row[0]:row[1:] for row in oldrows}; new_map={row[0]:row[1:] for row in new['source']}
need(len(oldrows)==len(old_map)==91 and old_map['g54']==['+','gamma','w'] and old_map['g56']==['*','U','g54'],'parent change shape')
need(set(old_map)-set(new_map)=={'g54'} and not(set(new_map)-set(old_map)),'row deletion mismatch')
for name,expr in new_map.items(): need(expr==(['*','U','direct'] if name=='g56' else old_map[name]),'row changed '+name)
known=set(new['witnesses']+new['fixed_numerals'])|set(range(5)); edges={}; counts=Counter()
for name,op,x,y in new['source']:
 need(name not in known and x in known and y in known and op in ('+','-','*'),'non-topological row '+name); known.add(name);edges[name]=(x,y); counts[op]+=1
seen=set(); pending=['P12']
while pending:
 n=pending.pop()
 if n in edges and n not in seen:seen.add(n);pending.extend(edges[n])
need(len(seen)==len(edges)==90 and dict(counts)=={'*':50,'+':23,'-':17},'wrong liveness/count')
need(new['operations']==90 and new['operation_breakdown']==dict(counts) and new['parent_graph_sha256']==sha(parent),'metadata mismatch')
need(rec['exit']==0 and rec['reason'] is None and rec['union_unchanged'] and rec['union_count']==1291 and rec['base_receipt_sha256']==sha(B),'Lean receipt mismatch')
need(rec['source_sha256']==rec['source_after']==sha(P/'DirectMainGraph.lean')==sha(O/'source.txt') and rec['runner_sha256']==rec['runner_after']==sha(P/'run-graph.py'),'source/runner mismatch')
need(rec['lean_sha256']==rec['lean_after']==sha(rec['command'][0]),'Lean mismatch')
need(rec['stdout_sha256']==sha(O/'stdout') and rec['stderr_sha256']==sha(O/'stderr') and not (O/'stderr').read_bytes(),'Lean log mismatch')
expected=''.join(f"'FreeJDirectMainGraph.{n}_eval' depends on axioms: [propext]\n" for n in ('first','main','ordinary'))
need((O/'stdout').read_text()==expected,'axiom log mismatch')
out=Path(rec['command'][rec['command'].index('-o')+1]); src=Path(rec['command'][rec['command'].index('-o')-1]);need(sha(out)==rec['object_sha256']=='fc4e4c2f55ead02cd216f1225933650e9ecfec11251a76def53f886380ec3f31' and sha(src)==sha(P/'DirectMainGraph.lean'),'source/object mismatch')
paths=rec['lean_path'].split(':'); producer=Path(paths[0])/'XQ91.olean';need(sha(producer)==rec['xq91_producer_sha256']=='747df97728f8c8125c205a752a6a2cbe205ce243cf2612ac57614025050be17d','selected producer mismatch')
need(base['exit']==0 and base['union_unchanged'] and len(rec['samples'])==2 and all(x['mem_available_kib']>=8*1024**2 and len(x['lean'])<=2 for x in [rec['preflight']]+rec['samples']),'recorded guard mismatch')
lib=Path(paths[1])
def union():
 files={p.relative_to(lib).as_posix():p for p in lib.rglob('*') if p.is_file()};need(len(files)==1291 and set(files)==set(base['union']),'union membership mismatch')
 for name,p in files.items():
  item=base['union'][name];need(p.is_symlink() and os.readlink(p)==item['link'] and str(p.resolve())==item['resolved'] and sha(p)==item['sha256'],'union mismatch '+name)
union();need(dr['exit']==0 and dr['checker_sha256']==sha(P/'check-dag.py') and dr['stdout_sha256']==sha(A/'stdout') and dr['stderr_sha256']==sha(A/'stderr') and not (A/'stderr').read_bytes(),'author DAG receipt mismatch')
run=subprocess.run([sys.executable,'-I','-S','-B',str(P/'check-dag.py')],capture_output=True,check=True);need(run.stdout==(A/'stdout').read_bytes() and not run.stderr,'author checker rerun mismatch')
union();checkpins();need(sha(out)==rec['object_sha256'] and sha(producer)==rec['xq91_producer_sha256'],'proof object changed')
print(json.dumps({'status':'PASS','source_rows':len(parsed),'live_rows':len(seen),'counts':dict(counts),'old_row_deleted':'g54','old_row_replaced':'g56','compiled_equalities':3,'selected_project_union':1291,'scope':'forward ring evaluations, external graph count; reverse existence and iPRA open'},indent=2))
