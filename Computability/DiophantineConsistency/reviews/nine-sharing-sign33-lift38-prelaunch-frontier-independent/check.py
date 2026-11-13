#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-lift38-check';draft=d/'research/nine-sharing-sign33-lift38-draft'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'6bdd4c85b0a9cb3117d7a5245ecf599f6f61507c514bc4403c40a64d3b12bf68','provider_survey.py':'36be3d2b0c178d33cc0e9be29cb6821b6daff24c3b70108c5823344d719355bb','source-manifest.json':'4320a76c9383f82adf498d944078c6f3af57e51896a9d0da37b78310166cbcfd','src/DiophantineConsistency/Sign33Lift38.lean':'fc0db4bb388bd6e044d6127ba3d0e8f5690c8420d07bf3a4cb9bfe7be59b0c87'}.items():assert h(p/n)==v
assert h(draft/'Sign33Lift38.lean')=='d78f21a96e5b5886ab21927c959c019ed8ff87c2764dd75530633e167a8eddb3' and h(draft/'check.py')=='a06aee26a623976fb54b437df1853bb76582dd5e9ad965e4c36230e8731a0006' and h(draft/'result.json')=='43948390b809692aca14425f8f543b3aa51681b9f617bfd056ffe2624e16cb45'
s=(p/'src/DiophantineConsistency/Sign33Lift38.lean').read_text();orig=(draft/'Sign33Lift38.lean').read_text();assert s.split('theorem lift_inputs',1)[0].rstrip()==orig.split('end DiophantineConsistency.Sign33Lift38',1)[0].rstrip()
assert re.findall(r'^theorem (\w+)',s,re.M)==['signed_values_of_all_cuts','lift_inputs','lift_signed_coordinates'];assert re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Sign33ResidualAssembly']
mapping=list(range(1,27))+[None,27,None,28,29,None,30,None,31,32,None,33];part=s.split('def lift ',1)[1].split('theorem signed_values',1)[0];actual=[None if t.strip()=='0' else int(t.strip()[2:]) for t in re.search(r'!\[(.*?)\]',part,re.S).group(1).split(',')];assert actual==mapping
assert 'lift v (Fin.castLE (by decide : 14 ≤ 38) i) = v (Fin.castLE (by decide : 15 ≤ 34) (Fin.succ i))' in s
signed=s.split('theorem lift_signed_coordinates',1)[1].split(':= by',1)[0];pairs=re.findall(r'lift v (\d+) = (?:v (\d+)|(0))',signed);assert len(pairs)==10
for i,j,z in pairs:assert mapping[int(i)]==(int(j) if j else None)
assert [int(i) for i,_,_ in pairs]==[25,26,27,28,30,31,32,33,36,37]
sv=s.split('def signedValues ',1)[1].split('def lift ',1)[0];assert [int(x) for x in re.findall(r'ι \(v (\d+)\)',sv)]==[26,27,29,30,33]
assembly=(d/'research/nine-sharing-sign33-residual-assembly-check/src/DiophantineConsistency/Sign33ResidualAssembly.lean').read_text();parts=s.split('theorem signed_values_of_all_cuts',1)[1].split(':= by',1)[0].rsplit(' :\n',1)[-1].split('∧');refs=[('04',0),('04',1),('05',2),('06',0),('07',0)]
for i,(batch,pos) in enumerate(refs):
 f=re.search(r'  batch'+batch+r' :\n(.*?)(?=\n  batch\d\d :|\n\ntheorem)',assembly,re.S).group(1).split('∧')[pos];left,right=f.split('=',1);u,v=parts[i].split('=',1);assert re.sub(r'\s+','',u)==f'signedValuesv{i}' and re.sub(r'\s+','',right)==re.sub(r'\s+','',v)
assert 'hc.batch04.1, hc.batch04.2.1, hc.batch05.2.2,' in s and 'hc.batch06.1, hc.batch07.1' in s
rs=subprocess.run([sys.executable,'-I','-S','-B',str(draft/'check.py')],capture_output=True,check=True);assert not rs.stderr and rs.stdout==(draft/'result.json').read_bytes()
x=json.loads((d/'research/nine-sharing-quartic65-norm38-candidate/seed.json').read_text());y=json.loads((d/'research/nine-sharing-quartic65-sign33-candidate/seed.json').read_text());assert len(x['gate_records'])==len(y['gate_records'])==60 and x['source_graph_sha256']==y['source_graph_sha256'] and x['fixed_ports']==y['fixed_ports']
for a,b in zip(x['gate_records'],y['gate_records']):
 assert all(a[k]==b[k] for k in ('kind','name','left','right','op'))
 if b['kind']=='materialized':
  if 'sign_coordinate' in b:
   v=b['sign_coordinate'];assert (mapping[a['positive_coordinate']-1],mapping[a['negative_coordinate']-1])==((v,None) if b['sign']==1 else (None,v))
  else:assert mapping[a['positive_coordinate']-1]==b['positive_coordinate']
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(z.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'graph_rows':60,'signed_values':5,'lift_positions':38,'scope':'uncompiled coordinate lift; no Lean gate or norm proof'},sort_keys=True,indent=2))
