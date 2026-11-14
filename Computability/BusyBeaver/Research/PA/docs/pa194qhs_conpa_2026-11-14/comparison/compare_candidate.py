#!/usr/bin/env python3
import argparse,json,hashlib
from pathlib import Path
from audit_inventory import parse,classify
p=argparse.ArgumentParser();p.add_argument('candidate',type=Path);p.add_argument('--inventory',type=Path,default=Path(__file__).parent/'census_full'/'tables.json');p.add_argument('--output',type=Path);a=p.parse_args()
data=a.candidate.read_bytes();v=classify(parse(data));tables=json.loads(a.inventory.read_text());hits=[x for x in tables if x['symmetry_rootfree_sha256']==v['symmetry_rootfree_sha256']]
r={'inventory_sha256':hashlib.sha256(a.inventory.read_bytes()).hexdigest(),'inventory_byte_forms':len(tables),'corpus_spanning194_classes':len({x['rootfree_sha256'] for x in tables if x['working_states']==194 and x['max_graph_reachable']==194}),'candidate_sha256':hashlib.sha256(data).hexdigest(),**v,'equivalence':'maximal rooted transition graph under arbitrary state renaming, any maximally reaching root, global L/R reflection, global read/write-bit interchange; halt row write and direction preserved','matches':[{'sha256':x['sha256'],'locators':x['locators']} for x in hits]}
if a.output:a.output.write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
