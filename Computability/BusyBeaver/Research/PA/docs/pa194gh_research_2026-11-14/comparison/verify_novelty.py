#!/usr/bin/env python3
"""Offline exact novelty, control counts, and direct-congruence replay.

Run: python3 verify_novelty.py --references tables --output replay.json CANDIDATE.tm ...
Requires this directory's audit.py; uses only the Python standard library.
Reference machines need not use the same labels or designate the same start.
"""
import argparse,collections,hashlib,json
from pathlib import Path
from audit import parse,canonical,encode,bisimulation_count,rooted

def inspect(path):
    data=path.read_bytes();rows,states,start,declared=parse(data)
    if len(states)!=194:raise ValueError(f'{path}: expected 194 working states')
    exact=canonical(rows,states)
    if exact is None:raise ValueError(f'{path}: no graph-spanning root')
    strong=min(canonical(rows,states,mirror=m,flip=f,loose=True)
               for m in (False,True) for f in (False,True))
    indegrees=collections.Counter(n for w,d,n in rows.values() if n in set(states))
    histogram=tuple(sorted(collections.Counter(indegrees[q] for q in states).items()))
    return {'path':str(path),'sha256':hashlib.sha256(data).hexdigest(),
            'states':len(states),'rows':len(rows),'start_metadata':start,
            'start_declared':declared,'reachable_from_start':rooted(rows,set(states),start)[1] if start is not None else None,
            'canonical_class':hashlib.sha256(encode(exact)).hexdigest(),
            'strong_class':hashlib.sha256(encode(strong)).hexdigest(),
            'indegree_histogram':histogram,
            'direct_congruence_states':bisimulation_count(rows,states),
            '_exact':exact,'_strong':strong}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--references',type=Path,default=Path(__file__).parent/'tables')
    ap.add_argument('--output',type=Path,required=True);ap.add_argument('--expected-count',type=int,default=94)
    ap.add_argument('candidates',type=Path,nargs='+');a=ap.parse_args()
    references=[inspect(p) for p in sorted(a.references.glob('*.tm'))]
    candidates=[inspect(p) for p in a.candidates]
    if len(references)!=a.expected_count:raise ValueError('reference corpus has the wrong number of representatives')
    for c in candidates:
        c['exact_matches']=[r['path'] for r in references if r['_exact']==c['_exact']]
        c['strong_matches']=[r['path'] for r in references if r['_strong']==c['_strong']]
        c['indegree_histogram_matches']=[r['path'] for r in references if r['indegree_histogram']==c['indegree_histogram']]
        if c['start_metadata']!=0 or c['reachable_from_start']!=194:
            raise ValueError('candidate needs the stated dense start0 and 194 graph-reachable controls')
        if c['strong_matches']:raise ValueError('candidate duplicates an existing graph')
    for i,c in enumerate(candidates):
        for d in candidates[:i]:
            if c['_strong']==d['_strong']:raise ValueError('candidate pair duplicates')
    for r in references+candidates:r.pop('_exact');r.pop('_strong')
    receipt={'status':'PASS','comparison':'Exact canonical tuples from every spanning root; state renaming; tape reflection; global bit exchange; terminal write/move ignored.',
      'bit_exchange_caution':'A structural exclusion test; global bit exchange alone changes the zero-blank convention.',
      'congruence_scope':'Immediate-transition congruence preserving written symbols and directions, with terminal kept separate. This is not a bound on arbitrary semantically equivalent machines.',
      'reference_count':len(references),'candidate_count':len(candidates),'candidates':candidates,
      'reference_congruence_counts':dict(collections.Counter(r['direct_congruence_states'] for r in references)),
      'reference_histograms':[{'path':r['path'],'sha256':r['sha256'],'indegree_histogram':r['indegree_histogram']} for r in references]}
    a.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='reference_histograms'},indent=2))
if __name__=='__main__':main()
