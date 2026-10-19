from pathlib import Path
import sys,json
SRC=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else Path(__file__).resolve().parent.parent/'sources/context246/zfc-context246'
sys.path.insert(0,str(SRC/'code'))
import review_affine_source as a
sites=a.parse_source(SRC/'sources/Prog254.v')[1]
affine=a.module(SRC/'sources/prior/prefix_affine.py')
out={}
for name in ('gap103','posL73','posR73','gap103posL73','gap103posR73'):
 p=Path(__file__).parent/(name+'.tm')
 a.TABLE_SHA256=a.digest(p)
 table=a.read_tm(p)
 out[name]=a.check_sites(affine,table,sites)
 print(name,out[name],flush=True)
(Path(__file__).parent/'neutral_site_proofs.json').write_text(json.dumps(out,indent=2)+'\n')
