#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-path18-27-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'9e03c4294480e64ae865208d494def2f537045d3f650c947643cb5a4057a113d','provider_preflight.py':'7c5a5449ef53d5901ebdee6fb1d6c15daa16303c911f727a88ffda3b038e6a11','source-manifest.json':'5165049bdc1dac38db9cdf44f8a04365f86cabd7eae186b28d7e555e729cba71','src/DiophantineConsistency/Norm38MacroPath18to27.lean':'efae242aed7e8139a7fe5c4adc67bbc8574fefa2830a02bee7b5cdfccfd3fb18'}.items():assert sha(p/n)==h
s=(p/'src/DiophantineConsistency/Norm38MacroPath18to27.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='efae242aed7e8139a7fe5c4adc67bbc8574fefa2830a02bee7b5cdfccfd3fb18';assert re.findall(r'^import ([\w.]+)$',s,re.M)==rows[0]['imports']==['DiophantineConsistency.Norm38MacroPath18to20'];assert re.findall(r'^theorem (\w+)',s,re.M)==['path18_27','lookup18_27'];assert re.findall(r'^#print axioms (\w+)',s,re.M)==['path18_27','lookup18_27']
theorem=s.split('theorem path18_27',1)[1].split('theorem lookup18_27',1)[0];assert 'PrefixPath d18 d27' in theorem and theorem.count('.castSucc')==9 and theorem.count('PrefixPath.step')==7 and theorem.count('Dag.snoc')==7 and 'path18_20' in theorem
lookup=s.split('theorem lookup18_27',1)[1].split('#print',1)[0];assert 'd27.values a ' in lookup and '= d18.values a i' in lookup and lookup.count('.castSucc')==9 and 'lookup path18_27 a i' in lookup
nodes=(d/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text()
for j in range(21,28):assert f'def d{j} : Dag {j} := .snoc d{j-1} ' in nodes
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'concrete nine-snoc path source and point-provider review; no Lean replay'},indent=2,sort_keys=True))
