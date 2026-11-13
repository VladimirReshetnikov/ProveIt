#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-dependent06-staged-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(P/'run.py')=='f7d24112fa4e224ec1fde38c35480e8723f6ac7ffbe0fcdd698801edc0e0baeb' and H(P/'source-manifest.json')=='19533c1679cc0e109198a5ce1fc7d33f7e9f190c6b51191462f4ee06bcb5ff48'
m=json.loads((P/'source-manifest.json').read_text())['rows'];names=['Jcarry','Gprime','Hcarry','H'];assert [r['module'].split('.')[-1] for r in m]==['Sign33MacroDependent'+n for n in names];ss=[]
for row,n,dep in zip(m,names,['Sign33MacroDependentF','Sign33MacroDependentJcarry','Sign33MacroDependentGprime','Sign33MacroDependentHcarry']):
 f=P/'src/DiophantineConsistency'/f'Sign33MacroDependent{n}.lean';old=D/'research/nine-seed38-jones-dependent06-staged-check/src/DiophantineConsistency'/f'Norm38MacroDependent{n}.lean';s=f.read_text();assert s==old.read_text().replace('Norm38','Sign33') and H(f)==row['source_sha256'] and row['imports']==['DiophantineConsistency.'+dep];ss.append(s)
for s,n,node,indices in [(ss[1],'Gprime',33,[23,31,26,29,23]),(ss[3],'H',34,[24,16,26])]:
 h=s.split('theorem prefix_'+n,1)[1].split(':= by',1)[0];assert f'd{node}.values a (Fin.last {node-1})' in h and [int(x) for x in re.findall(r'd\d+.values a ⟨(\d+), by decide⟩',h)]==indices
for s,n,start,end in [(ss[0],'d25_j_carry',24,18),(ss[1],'d32_A_carry',31,24),(ss[1],'d32_C_carry',31,27),(ss[1],'d32_D_carry',31,30),(ss[2],'d33_j_carry',32,25),(ss[2],'d33_Bprime_carry',32,25),(ss[3],'d33_C_carry',32,27)]:
 seg=s.split('theorem '+n,1)[1].split('\ntheorem ',1)[0];assert [int(x) for x in re.findall(r'exact Sign33MacroCuts.snoc_previous a d(\d+)',seg)]==list(range(start,end-1,-1)),n
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','stages':4,'scope':'local d33/d34 Gprime/H equations and prior-entry carries only'},sort_keys=True,indent=2))
