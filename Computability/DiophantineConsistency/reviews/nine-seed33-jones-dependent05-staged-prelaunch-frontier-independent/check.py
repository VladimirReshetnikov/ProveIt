#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-dependent05-staged-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(P/'run.py')=='41308332d2ea978c66e1e6ceed793c20446e662a6111064392d72b01740b4157' and H(P/'source-manifest.json')=='c249fba9416d5088ce3a648199dd000044323d0bf636584cbd16dfc9c19e720f'
m=json.loads((P/'source-manifest.json').read_text())['rows'];names=['Icarry','E','F'];assert [r['module'].split('.')[-1] for r in m]==['Sign33MacroDependent'+n for n in names];ss=[]
for row,n,dep in zip(m,names,['Sign33MacroDependentD','Sign33MacroDependentIcarry','Sign33MacroDependentE']):
 f=P/'src/DiophantineConsistency'/f'Sign33MacroDependent{n}.lean';old=D/'research/nine-seed38-jones-dependent05-staged-check/src/DiophantineConsistency'/f'Norm38MacroDependent{n}.lean';s=f.read_text();assert s==old.read_text().replace('Norm38','Sign33') and H(f)==row['source_sha256'] and row['imports']==['DiophantineConsistency.'+dep];ss.append(s)
for s,n,node,indices in [(ss[1],'E',31,[15,27,29,26]),(ss[2],'F',32,[23,30])]:
 h=s.split('theorem prefix_'+n,1)[1].split(':= by',1)[0];assert f'd{node}.values a (Fin.last {node-1})' in h and [int(x) for x in re.findall(r'd\d+.values a ⟨(\d+), by decide⟩',h)]==indices
for s,n,chain in [(ss[0],'d24_i_carry',list(range(23,17,-1))),(ss[1],'d30_i_carry',list(range(29,23,-1))),(ss[1],'d30_J_carry',[29,28]),(ss[1],'d30_C_carry',[29,28,27]),(ss[2],'d31_A_carry',list(range(30,23,-1)))]:
 seg=s.split('theorem '+n,1)[1].split('\ntheorem ',1)[0];assert [int(x) for x in re.findall(r'exact Sign33MacroCuts.snoc_previous a d(\d+)',seg)]==chain,n
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','stages':3,'scope':'local d31–d32 E/F prefix equations and prior-entry carries only'},sort_keys=True,indent=2))
