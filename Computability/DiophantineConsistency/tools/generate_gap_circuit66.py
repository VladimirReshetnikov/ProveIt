#!/usr/bin/env python3
"""Emit kernel-checked443/450-operation H2082 circuit data from pinned inert JSON."""
import argparse,collections,hashlib,importlib.util,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
DATA=ROOT/'candidates/gap2082-compact54/generated'
PINS={'positive':'7a34fddb23453755a26c9185f3540d99bc7697848e037fecbaa20fc2df7631a9',
      'natural':'be7d9e1285a1cf674978058c3b1be2f27a17af9c0d0bdc6e4f8310481a40d001'}
VARIABLES=['b','g','h','s','w','C','i','j','n']
FIXED=['base_scale','c_1f49e78f6521d0fe','c_bd70eebd66b6d548','c_e3dd773f14077424',
 'c_33afcc0215e266df','c_50b8a3599b18e0a9','c_e24dea94f889b837','c_d048f06bd476e521',
 'c_f69b40d0743298dc','c_a749e84ec6806d92','threshold_6480184']
s=importlib.util.spec_from_file_location('parent',ROOT/'tools/generate_split_circuit59.py')
g=importlib.util.module_from_spec(s);s.loader.exec_module(g)
require=g.require

def read(domain):
 raw=(DATA/f'gap2082_{domain}.json').read_bytes();require(hashlib.sha256(raw).hexdigest()==PINS[domain],'SHA256 '+domain)
 d=json.loads(raw);require(d['variables']==VARIABLES,'input order');nodes=d['nodes'];out=d['output'];parents=[[]for _ in nodes]
 require(d['source_sha256']=='e4f50dbede42c421defa2d7d36268413351dd1e023763c584ea34f3b9a827957','source pin')
 require(d['layout_sha256']=='d4b85e61d6cc88a385d608f11a938f8b36bf4280940f4d236be897573d3b6f51','layout pin')
 for i,n in enumerate(nodes):
  k=n['kind']
  if k=='variable':require(set(n)=={'kind','name'}and n['name']in VARIABLES,'input')
  elif k=='fixed':require(set(n)=={'kind','name'}and n['name']in FIXED,'fixed')
  elif k=='literal':require(set(n)=={'kind','value'}and type(n['value'])is int,'literal')
  else:
   require(k in['add','sub','mul']and set(n)=={'kind','left','right'},'binary kind')
   for j in[n['left'],n['right']]:require(type(j)is int and 0<=j<i,'topology');parents[j].append(i)
 require(type(out)is int and out==len(nodes)-1,'last output')
 live=set();todo=[out]
 while todo:
  i=todo.pop()
  if i in live:continue
  live.add(i)
  if nodes[i]['kind']in['add','sub','mul']:todo.extend([nodes[i]['left'],nodes[i]['right']])
 require(live==set(range(len(nodes))),'liveness')
 c=collections.Counter(n['kind']for n in nodes)
 expected={'positive':{'add':158,'sub':22,'mul':263},'natural':{'add':166,'sub':21,'mul':263}}[domain]
 require({k:c[k]for k in expected}==expected,'binary counts')
 require(d['operation_counts']==expected and d['total_operations']==sum(expected.values()),'claimed counts')
 require((c['variable'],c['fixed'],c['literal'])==(9,11,14),'leaf counts')
 require({n['name']for n in nodes if n['kind']=='variable'}==set(VARIABLES),'all inputs')
 require({n['name']for n in nodes if n['kind']=='fixed'}==set(FIXED),'all fixed')
 require(all(type(i)is int and 0<=i<len(nodes)for i in d['named_nodes'].values()),'named indices')
 return d,[min(parents[i])for i in range(out)]

def render():
 # Reuse only the checked generic output template; no upstream file is modified.
 g.read=read;g.PINS=PINS;g.VARIABLES=VARIABLES;g.FIXED=FIXED
 text=g.render().replace('SplitCircuit59','GapCircuit66').replace('generate_split_circuit59.py','generate_gap_circuit66.py')
 text=text.replace('compact54-sharp split116','compact54-sharp H2082').replace('Fin 12','Fin 11').replace('Node 9 12','Node 9 11').replace('Fixed leaves are12','Fixed leaves are11')
 text=re.sub(r'(kindCount \w+Nodes 2 = )12',r'\g<1>11',text)
 return text

if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');a=ap.parse_args()
 p=ROOT/'Lean/DiophantineConsistency/GapCircuit66.lean';text=render()
 if a.check:require(p.read_text()==text,'generated circuit differs')
 else:p.write_text(text)
 print(json.dumps({'status':'PASS'if a.check else'GENERATED','pins':PINS,'operations':[443,450],'inputs':9,'fixed':11},sort_keys=True))
