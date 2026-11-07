#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-live18-staged-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(P/'run.py')=='4a379a90b42ad4b154d51564baca9c1d6fd547aba345088aae95002040b3bd8e' and H(P/'source-manifest.json')=='fc595a8c30d84616ed338917c5f78ca0d9415a5b03703d94c0844e068a0e6d56'
m=json.loads((P/'source-manifest.json').read_text())['rows'];groups=[[('b',0,11),('N',3,11),('g',7,11)],[('G',9,11),('R',10,11),('h',11,12)],[('s',12,13),('w',13,14),('phi',14,15)],[('i',15,16),('j',16,17)]];assert len(m)==4
for j,(row,thms) in enumerate(zip(m,groups),1):
 name=f'Sign33MacroLive18Group{j:02d}';f=P/'src/DiophantineConsistency'/f'{name}.lean';s=f.read_text();old=D/'research/nine-seed38-jones-live18-staged-check/src/DiophantineConsistency'/f'Norm38MacroLive18Group{j:02d}.lean';assert s==old.read_text().replace('Norm38','Sign33') and H(f)==row['source_sha256'] and row['imports']==['DiophantineConsistency.Sign33MacroRankSymbolic']
 for n,k,end in thms:
  seg=s.split('theorem d18_'+n+'_carry',1)[1].split('\ntheorem ',1)[0];head=seg.split(':= by',1)[0];assert f'd18.values a ((Fin.last {k})'+'.castSucc'*(17-k)+')' in head and f'd{end}.values a ((Fin.last {k})'+'.castSucc'*(end-k-1)+')' in head
  assert [int(x) for x in re.findall(r'exact Sign33MacroCuts.snoc_previous a d(\d+)',seg)]==list(range(17,end-1,-1)),n
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','stages':4,'identities':11,'scope':'d18 live-entry preservation only'},sort_keys=True,indent=2))
