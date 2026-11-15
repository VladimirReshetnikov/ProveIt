#!/usr/bin/env python3
"""Compare complete candidate tuples against the pinned 194-state census.

Permitted structural symmetries: arbitrary control renaming, any spanning
root, reflection, global symbol exchange, and ignored final write/move.
This is a structural comparison, not a semantic correctness test.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json
HERE=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('current_census',HERE/'rebuild_current_census.py')
c=importlib.util.module_from_spec(s);s.loader.exec_module(c)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('tables',type=Path,nargs='+')
    ap.add_argument('--corpus',type=Path,default=HERE/'current')
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    refs={k:tuple(tuple(row) for row in v) for k,v in json.loads((args.corpus/'canonical_tuples194.json').read_text()).items()}
    result={'reference_count':len(refs),'claim':'Exact structural novelty only; no halting or arithmetic theorem.','candidates':[]}
    seen={}
    for p in args.tables:
        b=p.read_bytes();data=c.ji.lib.parse_table(b)
        if data is None:raise ValueError('Not a complete binary one-halt table: '+str(p))
        rows,states,halt=data;forms=[]
        for q in states:
            for mirror in (False,True):
                for complement in (False,True):
                    t,n=c.full_tuple(data,q,mirror,complement,True)
                    if n==len(states):forms.append(t)
        if not forms:raise ValueError('Candidate has no spanning root: '+str(p))
        t=min(forms);matches=[key for key,v in refs.items() if v==t]
        dup=seen.get(t);seen[t]=str(p)
        result['candidates'].append({'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'states':len(states),'rows':len(rows),'enlarged_symmetry_sha256':hashlib.sha256(json.dumps(t,separators=(',',':')).encode()).hexdigest(),'exact_matches':matches,'matches_earlier_candidate':dup,'new_structural_class':not matches and dup is None})
    text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text)
if __name__=='__main__':main()
