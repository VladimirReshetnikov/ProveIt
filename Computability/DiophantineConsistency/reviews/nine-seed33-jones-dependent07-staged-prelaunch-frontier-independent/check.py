#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-dependent07-staged-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(P/'run.py')=='ea482651d28a32a624d6937535e92c0504b358baf4adf6b2153e8f0df60ee736' and H(P/'source-manifest.json')=='2750add09acd2fd99d36d804dc1ffc5f39efd1a2b16bc900822bc539d2e5a1b7'
m=json.loads((P/'source-manifest.json').read_text())['rows'];names=['I','A0Early','A0','A1','V'];assert [r['module'].split('.')[-1] for r in m]==['Sign33MacroDependent'+n for n in names];ss=[]
for row,n,dep in zip(m,names,['Sign33MacroDependentH','Sign33MacroDependentI','Sign33MacroDependentA0Early','Sign33MacroDependentA0','Sign33MacroDependentA1']):
 f=P/'src/DiophantineConsistency'/f'Sign33MacroDependent{n}.lean';old=D/'research/nine-seed38-jones-dependent07-staged-check/src/DiophantineConsistency'/f'Norm38MacroDependent{n}.lean';s=f.read_text();assert s==old.read_text().replace('Norm38','Sign33') and H(f)==row['source_sha256'] and row['imports']==['DiophantineConsistency.'+dep];ss.append(s)
for s,n,node,indices in [(ss[0],'I',35,[32,33]),(ss[2],'A0',36,[21,22]),(ss[3],'A1',37,[29,31,34]),(ss[4],'V0',38,[35]),(ss[4],'V1',39,[36])]:
 h=s.split('theorem prefix_'+n,1)[1].split(':= by',1)[0];assert f'd{node}.values a (Fin.last {node-1})' in h and [int(x) for x in re.findall(r'd\d+.values a ⟨(\d+), by decide⟩',h)]==indices
for s,n,start,end in [(ss[0],'d34_Gprime_carry',33,33),(ss[1],'d28_P_carry',27,22),(ss[1],'d29_K_carry',28,23),(ss[2],'d35_P_carry',34,28),(ss[2],'d35_K_carry',34,29),(ss[3],'d36_D_carry',35,30),(ss[3],'d36_F_carry',35,32),(ss[3],'d36_I_carry',35,35),(ss[4],'d37_A0_carry',36,36),(ss[4],'d38_A1_carry',37,37)]:
 seg=s.split('theorem '+n,1)[1].split('\ntheorem ',1)[0];assert [int(x) for x in re.findall(r'exact Sign33MacroCuts.snoc_previous a d(\d+)',seg)]==list(range(start,end-1,-1)),n
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','stages':5,'scope':'local d35–d39 I/A0/A1/V nodes and prior carries only'},sort_keys=True,indent=2))
