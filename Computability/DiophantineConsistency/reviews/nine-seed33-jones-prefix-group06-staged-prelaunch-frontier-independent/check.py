#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-prefix-group06-staged-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(P/'run.py')=='49bb6396d0128870498e2b83366daa0fc227251a9b2d7c87041fc670119c7a6c' and H(P/'source-manifest.json')=='820cc9621d86a43cebb85009e97dc540dba5a2ec33f195692f02a352a74fb833'
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert [x['module'] for x in m]==['DiophantineConsistency.Sign33MacroPrefixCarrySums','DiophantineConsistency.Sign33MacroPrefixCarryOthers']
checks=[('CarrySums',[('e',4,5),('ell',5,6),('lambda',6,7)]),('CarryOthers',[('g',7,8),('theta',8,9),('B',1,9),('b',0,9)])]
for row,(suffix,thms) in zip(m,checks):
 f=P/'src/DiophantineConsistency'/f'Sign33MacroPrefix{suffix}.lean';s=f.read_text();old=D/'research/nine-seed38-jones-prefix-group06-staged-check/src/DiophantineConsistency'/f'Norm38MacroPrefix{suffix}.lean';assert s==old.read_text().replace('Norm38','Sign33') and H(f)==row['source_sha256'] and row['imports']==['DiophantineConsistency.Sign33MacroPrefixQNCarry']
 for name,index,end in thms:
  seg=s.split('theorem d10_'+name+'_carry',1)[1].split('\ntheorem ',1)[0];head=seg.split(':= by',1)[0];assert f'd10.values a ((Fin.last {index})'+'.castSucc'*(9-index)+')' in head and f'd{end}.values a ((Fin.last {index})'+'.castSucc'*(end-index-1)+')' in head
  assert [int(x) for x in re.findall(r'exact Sign33MacroCuts.snoc_previous a d(\d+)',seg)]==list(range(9,end-1,-1))
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','stages':2,'identities':7,'scope':'d10 preservation equalities to earlier short prefixes only'},sort_keys=True,indent=2))
