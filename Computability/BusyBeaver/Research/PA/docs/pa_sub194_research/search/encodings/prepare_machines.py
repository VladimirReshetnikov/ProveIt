#!/usr/bin/env python3
"""Materialize uniform search inputs from the supplied pinned packets."""
from pathlib import Path
import argparse,importlib.util,json,shutil,sys,hashlib

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent.parent
ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,default=ROOT/'ProveIt');ap.add_argument('--incoming',type=Path,default=ROOT/'incoming_extracted');a=ap.parse_args()
INCOMING=a.incoming
PA=a.repo/'Computability/BusyBeaver/Research/PA/docs'
OUT=HERE/'machines';OUT.mkdir(exist_ok=True)
manifest=[]
def package(name,dense,labels,sites,ins,physical=None):
    out=OUT/name;out.mkdir(exist_ok=True)
    label=json.loads(labels.read_text());native=[]
    for line in dense.read_text().splitlines():
        if not line.strip() or line.startswith('#'):continue
        q,b,w,d,n=line.split();native.append((label[int(q)],int(b),int(w),d,label[int(n)]))
    (out/'machine.tm').write_bytes(dense.read_bytes())
    (out/'machine.native.tm').write_text(''.join(f'{q} {b} {w} {d} {n}\n' for q,b,w,d,n in sorted(native)))
    (out/'labels.json').write_bytes(labels.read_bytes())
    if isinstance(sites,Path):sites=json.loads(sites.read_text())
    if isinstance(ins,Path):ins=json.loads(ins.read_text())
    sites=[[''.join(map(str,p)),op,arg] for p,op,arg in sites]
    (out/'sites.json').write_text(json.dumps(sites)+'\n')
    (out/'instructions.json').write_text(json.dumps(ins)+'\n')
    manifest.append(dict(name=name,input_dir='machines/'+name,source_dense=str(dense),source_labels=str(labels),sha256=hashlib.sha256(dense.read_bytes()).hexdigest(),physical=physical or '6,2,0,4,3,7,8,5,1'))

p=PA/'pa194_conpa_2026-11-13/construction'
package('primary',p/'tables/pa194.tm',p/'tables/pa194.labels.json',p/'source/pa194.sites.json',p/'source/pa194.instructions.json')
for name,packet in [('DHS','pa194dhs_conpa_2026-11-13'),('QN','pa194qn_research_2026-11-13'),('H6','pa194h6_conpa_2026-11-13')]:
    p=INCOMING/packet/packet/'machine';package(name,p/'machine.tm',p/'labels.json',p/'sites.json',p/'instructions.json')
p=INCOMING/'pa194haz_research_2026-11-14/pa194haz_research_2026-11-14/machine'
for name,stem in [('HA','pa194ha'),('HAZ','pa194haz')]:
    package(name,p/(stem+'.tm'),p/(stem+'.labels.json'),p/(stem+'.sites.json'),p/(stem+'.instructions.json'),'6,2,0,3,4,7,8,5,1')
p=INCOMING/'PA194NS_research/PA194NS_research'
sys.path.insert(0,str(p));spec=importlib.util.spec_from_file_location('ns_verify_inputs',p/'verify.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
g=v.c.read_grammar(p/'baseline/grammar.json')
for name,nopush,stem in [('SUMS',False,'pa194sums'),('NSsum',True,'pa194ns')]:
    sites,ins,cs=v.source(g,nopush,True)
    package(name,p/(stem+'.tm'),p/(stem+'.labels.json'),sites,ins)
(HERE/'machine_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(manifest,indent=2))
