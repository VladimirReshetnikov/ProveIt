"""Generate symbolic-label proofs for every natural substitution, not test instances."""
from pathlib import Path
import sys,json,hashlib,argparse
P=Path(__file__).resolve().parent
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args();assert __debug__ and not sys.flags.optimize
args.output.parent.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(P))
import merged_euclidean_helper_certificate as g
import combined_helper_certificate as h
g.kappa=lambda a,b:('kappa',a,b)
x,y,z='x','y','z'
roots={
 'reflexivity':g.reflexivity(x),
 'ordinary_helper':g.ordinary_helper(x,y),
 'equality_box_elim':g.equality_box_elim(x,y),
 'original_rho7':g.euclidean(x,y,z),
 'symmetry':g.symmetry(x,y),
 'merged_from_old':g.merged_from_old(x,y,z),
}
V=('opaque','V');J=('opaque','J');H=g.old_h(x,y).form
old=h.N(h.I(V,h.I(H,J)));new=h.N(h.I(V,J))
roots['old_bundle_to_new']=h.taut(h.I(old,new))
roots['old_bundle_to_helper']=h.taut(h.I(old,H))
roots['new_bundle_plus_helper_to_old']=h.taut(h.I(new,h.I(H,old)))
for t in roots.values():g.check(t,set(),{})
data=h.export(roots);data['format']='uniform-label-terms-v1';data['label_terms']='Variables x,y,z and kappa(a,b)=4*CantorPair(a,b)+1. Every natural substitution is allowed, including all equalities.'
out=args.output;out.write_text(json.dumps(data,separators=(',',':'))+'\n');print(len(data['proof_nodes']),len(data['formulas']),hashlib.sha256(out.read_bytes()).hexdigest())
