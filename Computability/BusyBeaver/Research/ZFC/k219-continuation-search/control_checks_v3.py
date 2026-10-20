"""Finite positive/negative controls for the local-filter acceptance machinery."""
from pathlib import Path
import argparse,hashlib,json
import search_v3 as search

root=Path(__file__).resolve().parent
inputs=json.loads((root/'inputs.json').read_text())
checker=search.load_checker((root/inputs['universal_checker']['path']).resolve())
# State2 makes an identity R/L/R detour to3; state1 reaches3 directly.
old={(0,0):(0,1,1),(0,1):(1,1,2),
     (1,0):(0,1,3),(1,1):(1,1,3),
     (2,0):(0,1,4),(2,1):(1,1,4),
     (4,0):(0,-1,5),(4,1):(1,-1,5),
     (5,0):(0,1,3),(5,1):(1,1,3),
     (3,0):(0,1,3),(3,1):(1,1,254)}
keep,drop=1,2
new={(q,b):(w,d,keep if z==drop else z) for(q,b),(w,d,z) in old.items() if q!=drop}
cases=[]
for radius in (3,5,7):
 inv=checker.domain(old,0,radius); paths={}
 assert search.local_filter(old,new,inv,keep,drop,paths,97,radius) is None
 positive=checker.check(old,new,0,0,keep,drop,radius,97,inv)
 assert positive['maximum_old_block']==3 and positive['maximum_new_block']==1
 bad=new.copy();bad[keep,0]=(0,1,254)
 failure=search.local_filter(old,bad,inv,keep,drop,paths,97,radius)
 assert failure is not None
 try:checker.check(old,bad,0,0,keep,drop,radius,97,inv)
 except ValueError as exc:negative=str(exc)
 else:raise AssertionError('Negative early halt accepted')
 cases.append({'radius':radius,'fuel':97,'positive':positive,'negative_filter':failure,'negative_checker':negative})
result={'status':'SYNTHETIC_NONTRIVIAL_MERGE_CONTROLS_PASS','cases':cases,'scope':'Known synthetic3/1 positive merge and invalid early halt. Validates these cases only, not all search rejections.','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'search_source_sha256':hashlib.sha256((root/'search_v3.py').read_bytes()).hexdigest()}
parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True)
output=parser.parse_args().output;assert not output.exists()
output.write_text(json.dumps(result,indent=2)+'\n');print(result['status'])
