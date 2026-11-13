#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-dependent03-staged-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(P/'run.py')=='92b3c11acea4ed6cb2c2436b866a7f953fcf2e79b8f2493f7eab75cf2c86de29' and H(P/'source-manifest.json')=='23df6e4471b27ea1a804a361d9d6b77a7cf925f443bc64468ba6474298d1c97c'
m=json.loads((P/'source-manifest.json').read_text())['rows'];names=['A','Bprime','W','C'];assert [r['module'].split('.')[-1] for r in m]==['Sign33MacroDependent'+n for n in names];ss=[]
for row,n,dep in zip(m,names,['Sign33MacroDependentK','Sign33MacroDependentA','Sign33MacroDependentBprime','Sign33MacroDependentW']):
 f=P/'src/DiophantineConsistency'/f'Sign33MacroDependent{n}.lean';old=D/'research/nine-seed38-jones-dependent03-staged-check/src/DiophantineConsistency'/f'Norm38MacroDependent{n}.lean';s=f.read_text();assert s==old.read_text().replace('Norm38','Sign33') and H(f)==row['source_sha256'] and row['imports']==['DiophantineConsistency.'+dep];ss.append(s)
for s,n,node,indices in zip(ss,names,[24,25,26,27],[[20,18],[10],[0,13],[24,25,14]]):
 h=s.split('theorem prefix_'+n,1)[1].split(':= by',1)[0];assert f'd{node}.values a (Fin.last {node-1})' in h and [int(x) for x in re.findall(r'd\d+.values a ⟨(\d+), by decide⟩',h)]==indices
for s,n,chain in [(ss[0],'d23_M_carry',[22,21]),(ss[0],'d23_U_carry',[22,21,20,19]),(ss[1],'d24_R_carry',[23,22,21,20,19,18]),(ss[2],'d25_b_carry',[24,23,22,21,20,19,18]),(ss[2],'d25_w_carry',[24,23,22,21,20,19,18]),(ss[3],'d26_phi_carry',[25,24,23,22,21,20,19,18])]:
 seg=s.split('theorem '+n,1)[1].split('\ntheorem ',1)[0];assert [int(x) for x in re.findall(r'exact Sign33MacroCuts.snoc_previous a d(\d+)',seg)]==chain,n
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','stages':4,'scope':'local d24–d27 A/Bprime/W/C and prior-entry carries only'},sort_keys=True,indent=2))
