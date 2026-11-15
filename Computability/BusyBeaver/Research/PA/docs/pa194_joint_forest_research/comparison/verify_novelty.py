#!/usr/bin/env python3
"""Portable exact graph-novelty check against the complete frozen194 frontier.

Usage: python3 comparison/verify_novelty.py candidate1.tm candidate2.tm
This does not establish consistency calibration or operational correctness.
"""
from pathlib import Path
import argparse, hashlib, json
import novelty_helpers as nh

HERE=Path(__file__).resolve().parent
def sha(b): return hashlib.sha256(b).hexdigest()
def enc(x): return json.dumps(x,separators=(',',':')).encode()
def require(p,msg):
    if not p: raise ValueError(msg)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('candidates',type=Path,nargs='+')
    ap.add_argument('--output',type=Path)
    ap.add_argument('--allow-known',action='store_true',help='Report rather than reject corpus matches, useful for positive controls.')
    args=ap.parse_args()
    manifest=json.loads((HERE/'reference_manifest.json').read_text())
    refs=[];nonspanning=[]
    for name,m in sorted(manifest['tables'].items()):
        data=(HERE/'reference_tables'/name).read_bytes()
        require(sha(data)==m['sha256'],'Reference hash mismatch: '+name)
        rows,states,start=nh.parse(data)
        c=nh.canonical(rows,states)
        if name.startswith('nonspanning_'):
            require(c is None,'Expected nonspanning graph: '+name)
            nonspanning.append(name);continue
        require(c is not None and sha(enc(c))==Path(name).stem,'Canonical class mismatch: '+name)
        s=nh.strong(rows,states)
        require(sha(enc(s))==m['class']['strong_class'],'Strong class mismatch: '+name)
        require(nh.bisimulation_count(rows,states)==194,'Unexpected ordinary quotient: '+name)
        refs.append((Path(name).stem,c,s))
    require(len(refs)==manifest['spanning_194_classes']==548,'Incorrect reference count')
    require(len(nonspanning)==manifest['nonspanning_194_tables']==2,'Incorrect nonspanning count')
    results=[];peers=[]
    for p in args.candidates:
        data=p.read_bytes();rows,states,start=nh.parse(data)
        require(start is not None and nh.reachable(rows,states,start)==194,'Candidate has no stated spanning start: '+str(p))
        c=nh.canonical(rows,states);s=nh.strong(rows,states)
        old=[k for k,rc,rs in refs if rc==c or rs==s]
        same=[k for k,rc,rs in peers if rc==c or rs==s]
        if not args.allow_known: require(not old and not same,'Known/cosmetic match: '+str(p))
        results.append({'candidate':str(p),'sha256':sha(data),'states':194,'rows':388,
                        'start':start,'start_reachable':194,'canonical_sha256':sha(enc(c)),
                        'strong_sha256':sha(enc(s)),'prior_matches':old,'peer_matches':same,
                        'bisimulation_states':nh.bisimulation_count(rows,states)})
        peers.append((str(p),c,s))
    result={'source_commit':manifest['source_commit'],'verified_spanning_reference_classes':len(refs),
            'verified_nonspanning_reference_tables':len(nonspanning),'candidates':results,'passed':True,
            'comparison':'Exact canonical tuples; arbitrary spanning start and state names; tape reflection; global symbol exchange; halt-edge write/move ignored.',
            'scope':'Graph novelty only. Global symbol exchange is not asserted to preserve fixed-zero-blank semantics. Nonspanning graphs cannot be isomorphic to these spanning candidates.'}
    text=json.dumps(result,indent=2)+'\n'
    if args.output: args.output.write_text(text)
    print(text,end='')

if __name__=='__main__': main()
