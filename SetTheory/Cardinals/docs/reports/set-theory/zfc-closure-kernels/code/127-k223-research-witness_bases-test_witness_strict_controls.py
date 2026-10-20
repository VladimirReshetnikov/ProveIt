#!/usr/bin/env python3
"""Bounded mutation controls for the independent witnessed-basis checker."""
from pathlib import Path
import hashlib,json,subprocess,sys,tempfile
A=Path(__file__).resolve().parent;L=A;checker=A/'check_witness_strict.py';results=[]
base=json.loads((L/'uniform_witness_tag1_dag.json').read_bytes())
with tempfile.TemporaryDirectory(prefix='witness_controls_')as td:
 td=Path(td);p=td/'bad.json';out=td/'receipt.json'
 def check(name,d,msg,sym=False):
  p.write_text(json.dumps(d,separators=(',',':'))+'\n');cmd=[sys.executable,'-B',str(checker),str(p),'--output',str(out)]+(['--symmetric']if sym else[]);r=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
  if r.returncode==0 or msg not in r.stdout:raise ValueError((name,r.returncode,r.stdout[-2000:]))
  results.append(dict(control=name,rejected=True,reason=msg));print(name,'REJECTED',flush=True)
 n=next(i for i,pf in enumerate(base['proof_nodes'])if pf['rule']=='MP');old=base['proof_nodes'][n]['args'][0];base['proof_nodes'][n]['args'][0]=-1;check('negative_mp_reference',base,'MP prior nonnegative indices');base['proof_nodes'][n]['args'][0]=old
 n=next(i for i,f in enumerate(base['formulas'])if f[0]=='all');old=base['formulas'][n][1];base['formulas'][n][1]=-1;check('negative_binder',base,'Invalid DAG binder/child');base['formulas'][n][1]=old
 n=next(i for i,pf in enumerate(base['proof_nodes'])if pf['rule']=='TAUT');old=base['proof_nodes'][n]['formula'];base['proof_nodes'][n]['formula']=next(i for i,f in enumerate(base['formulas'])if f[0]=='eq');check('false_boolean_tautology',base,'False Boolean tautology');base['proof_nodes'][n]['formula']=old
 name=next(iter(base['roots']));old=base['roots'][name];base['roots'][name]=0;check('wrong_closed_endpoint',base,'Wrong/open root');base['roots'][name]=old
 base=json.loads((L/'symmetric_witness_tag1_dag.json').read_bytes());base['proof_nodes'][0]['rule']='SYM';check('forbidden_primitive_symmetry',base,'Forbidden SYM in symmetric witness basis',True)
res=dict(status='INDEPENDENT_WITNESSED_BASIS_TAMPER_CONTROLS_PASS',controls=results,checker_sha256=hashlib.sha256(checker.read_bytes()).hexdigest());(A/'witness_strict_controls.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
