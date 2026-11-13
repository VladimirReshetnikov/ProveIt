#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-dependent02-staged-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(P/'run.py')=='04e098e11c26df54507915431e44f5364fcc0fd00e28ab0620d796e2b285eb62' and H(P/'source-manifest.json')=='368b6851d8516b63cdab1dc4ba495a6cfd911aaf970d5b0c3a7558bee6b849c6'
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert [r['module'].split('.')[-1] for r in m]==['Sign33MacroDependentM','Sign33MacroDependentP','Sign33MacroDependentK'];ss=[]
for row,n,dep in zip(m,['M','P','K'],['Sign33MacroDependentY','Sign33MacroDependentM','Sign33MacroDependentP']):
 f=P/'src/DiophantineConsistency'/f'Sign33MacroDependent{n}.lean';old=D/'research/nine-seed38-jones-dependent02-staged-check/src/DiophantineConsistency'/f'Norm38MacroDependent{n}.lean';s=f.read_text();assert s==old.read_text().replace('Norm38','Sign33') and H(f)==row['source_sha256'] and row['imports']==['DiophantineConsistency.'+dep];ss.append(s)
a,b,c=ss
for s,name,node,idx in [(a,'M',21,[10,19]),(b,'P',22,[20,18]),(c,'K',23,[10,11,21])]:
 seg=s.split('theorem prefix_'+name,1)[1].split(':= by',1)[0];assert f'd{node}.values a (Fin.last {node-1})' in seg and [int(x) for x in re.findall(r'd\d+.values a ⟨(\d+), by decide⟩',seg)]==idx
assert '((2 : Int) : R)' in b and '^ (2 : Nat)' in b and ' - ((1 : Int) : R)' in c
for s,name,chain in [(a,'d20_R_carry',[19,18]),(b,'d21_U_carry',[20,19]),(c,'d22_R_carry',[21,20,19,18]),(c,'d22_h_carry',[21,20,19,18])]:
 seg=s.split('theorem '+name,1)[1].split('\ntheorem ',1)[0];assert [int(x) for x in re.findall(r'exact Sign33MacroCuts.snoc_previous a d(\d+)',seg)]==chain
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','stages':3,'scope':'local M/P/K prefix equations and prior-entry carries only'},sort_keys=True,indent=2))
