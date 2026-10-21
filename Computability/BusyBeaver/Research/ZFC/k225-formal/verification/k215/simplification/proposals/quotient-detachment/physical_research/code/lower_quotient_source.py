#!/usr/bin/env python3
"""Lower missing primitive polarities in the eight quotient-MP source variants.

The right-hand CI6 wrapper clears R1, which is already zero at this interface.
This is an arithmetic source transformation, not a binary runtime certificate.
"""
from pathlib import Path
import argparse,sys,json,hashlib
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'code/vendor'))
import source_language as s,source_splice as sp
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();a.output.mkdir(exist_ok=False)
    old=s.tree(json.loads((ROOT/'inputs/sites215.json').read_text()));outcomes=[]
    def tup(v):return tuple(tup(x)for x in v)if isinstance(v,list)else v
    def lower(n,right=False):
        if s.leaf(n):
            if right and n==('CD',5):return ((n,('CB',1)),('CB',1))
            if right and n==('CI',6):return (n,(('CD',1),('CC',1)))
            return n
        return lower(n[0]),lower(n[1],True)
    for row in json.loads((ROOT/'quotient/sources/summary.json').read_text()):
        rep=lower((tup(row['division_tree']),(('CD',7),(('CI',5),('CC',2)))))
        assert s.boundary(rep)==(0,0,False)
        source=sp.apply_closed_splices(old,{(4652,4661):rep});raw=s.compact(s.sites(source));name='lowered_'+row['name'];dest=a.output/name;dest.mkdir();(dest/'sites.json').write_bytes(raw)
        expected=ROOT/'quotient/sources'/name/'sites.json';assert raw==expected.read_bytes()
        outcomes.append(dict(name=name,metrics=s.metrics(source),source_sha256=hashlib.sha256(raw).hexdigest()))
    (a.output/'receipt.json').write_text(json.dumps(outcomes,indent=2)+'\n');print(json.dumps(outcomes,indent=2))
if __name__=='__main__':main()
