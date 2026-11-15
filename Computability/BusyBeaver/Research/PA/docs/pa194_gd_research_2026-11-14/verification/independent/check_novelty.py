#!/usr/bin/env python3
"""Exact novelty against the complete retained current 194-control frontier."""
from pathlib import Path
import argparse,hashlib,json,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[1]/'comparison'))
from census_tables import parse,canonical

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--frontier',type=Path,default=HERE.parents[1]/'comparison/frontier194')
    ap.add_argument('--machines',nargs='+',type=Path,default=[HERE/'inputs'/n for n in('GD194sum','GD194H','GD194HS')])
    ap.add_argument('--output',type=Path,default=HERE/'novelty.json')
    args=ap.parse_args();ref={}
    for p in sorted(args.frontier.glob('*.tm')):
        c=canonical(parse(p.read_text()));assert c is not None
        k=hashlib.sha256(repr(c).encode()).hexdigest();assert k==p.stem
        ref[k]=c
    assert len(ref)==139
    new={};result={}
    for d in args.machines:
        b=(d/'machine.tm').read_bytes();c=canonical(parse(b.decode()));assert c is not None
        matches=[k for k,t in ref.items()if c==t];mutual=[k for k,t in new.items()if c==t]
        result[d.name]={'dense_sha256':hashlib.sha256(b).hexdigest(),'strong_class_sha256':hashlib.sha256(repr(c).encode()).hexdigest(),'old_frontier_classes':len(ref),'full_tuple_matches':matches,'matches_prior_new_candidates':mutual,'novel_against_current_139':not matches,'distinct_from_prior_new_candidates':not mutual}
        assert not matches and not mutual
        new[d.name]=c
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
