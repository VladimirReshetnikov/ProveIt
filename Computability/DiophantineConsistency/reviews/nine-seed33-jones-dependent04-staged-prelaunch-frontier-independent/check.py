#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-dependent04-staged-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(P/'run.py')=='27ea0e8a16895c4a19f73106be380c7a5071d9060a757cb233d12cf234154bd7' and H(P/'source-manifest.json')=='6a2024ca09a60893a01b2b0bcfbded643de929f6813037be2fd0d17869da3a43'
m=json.loads((P/'source-manifest.json').read_text())['rows'];names=['J','Q','D'];assert [r['module'].split('.')[-1] for r in m]==['Sign33MacroDependent'+n for n in names];ss=[]
for row,n,dep in zip(m,names,['Sign33MacroDependentC','Sign33MacroDependentJ','Sign33MacroDependentQ']):
 f=P/'src/DiophantineConsistency'/f'Sign33MacroDependent{n}.lean';old=D/'research/nine-seed38-jones-dependent04-staged-check/src/DiophantineConsistency'/f'Norm38MacroDependent{n}.lean';s=f.read_text();assert s==old.read_text().replace('Norm38','Sign33') and H(f)==row['source_sha256'] and row['imports']==['DiophantineConsistency.'+dep];ss.append(s)
for s,n,node,indices in zip(ss,names,[28,29,30],[[23],[25,26,25],[23,26]]):
 h=s.split('theorem prefix_'+n,1)[1].split(':= by',1)[0];assert f'd{node}.values a (Fin.last {node-1})' in h and [int(x) for x in re.findall(r'd\d+.values a ⟨(\d+), by decide⟩',h)]==indices
for s,n,chain in [(ss[0],'d27_A_carry',[26,25,24]),(ss[1],'d28_W_carry',[27,26]),(ss[1],'d28_C_carry',[27]),(ss[2],'d29_A_carry',[28,27,26,25,24]),(ss[2],'d29_C_carry',[28,27])]:
 seg=s.split('theorem '+n,1)[1].split('\ntheorem ',1)[0];assert [int(x) for x in re.findall(r'exact Sign33MacroCuts.snoc_previous a d(\d+)',seg)]==chain,n
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','stages':3,'scope':'local d28–d30 J/Q/D prefix equations and carries only'},sort_keys=True,indent=2))
