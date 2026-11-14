#!/usr/bin/env python3
"""Independently replay finite halts and provable blank rays of startup mutants.

A ray is certified only when the literal row on 0 is a self-loop moving into
an entirely blank half-line. Writing behind the head then preserves that
fact forever. This is a finite induction certificate, not an extrapolation
from a long bounded simulation. The coefficient-three calculus rejection is
recorded separately and its 73,393-line logical certificate is not rerun here.
"""
from pathlib import Path
import argparse,collections,hashlib,json
from check_novelty import parse

ROOT=Path(__file__).resolve().parent

def classify(rows,start,bound):
    q=start;p=0;ones=set()
    for steps in range(bound+1):
        if (q,0) not in rows:return {'status':'halt','steps':steps,'state':q,'head':p,'ones':sorted(ones)}
        read=int(p in ones);w,d,n=rows[q,read]
        if read==0 and n==q and ((d=='R' and not any(x>=p for x in ones)) or (d=='L' and not any(x<=p for x in ones))):
            return {'status':'ray','steps':steps,'state':q,'head':p,'ones':sorted(ones),'self_loop_row':[q,0,w,d,n]}
        if steps==bound:break
        if w:ones.add(p)
        else:ones.discard(p)
        p+=1 if d=='R' else -1;q=n
    return {'status':'unresolved','steps':bound,'state':q,'head':p,'ones':sorted(ones)}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--receipt',type=Path);ap.add_argument('--bound',type=int,default=2000);args=ap.parse_args()
    entries=json.loads((ROOT/'frontier193.json').read_text());details=[];totals=collections.defaultdict(collections.Counter)
    for entry in entries:
        data=(ROOT/entry['table_file']).read_bytes()
        if hashlib.sha256(data).hexdigest()!=entry['table_sha256']:raise ValueError('Hash mismatch')
        rows,states=parse(data)
        if len(states)!=193:raise ValueError('Wrong working-state count')
        starts=sorted(states) if entry['all_193_blank_starts_to_replay'] else [entry['single_start_to_replay']] if entry['single_start_to_replay'] is not None else []
        for start in starts:
            result=classify(rows,start,args.bound);details.append({'table_class':entry['table_class'],'initial_state':start,**result});totals[entry['category']][result['status']]+=1
    counts={k:dict(v) for k,v in totals.items()}
    if counts['startup-rejected transplant']!={'ray':9357,'halt':100}:raise ValueError(('Transplant results differ',counts))
    if counts['startup-rejected AX11 core']!={'ray':191,'halt':2}:raise ValueError(('AX11 results differ',counts))
    if any(r['status']=='unresolved' for r in details):raise ValueError('Some runs unresolved')
    result={'status':'PASS','tables_checked':len(entries),'blank_runs_checked':len(details),'run_bound':args.bound,'classification_totals':counts,'coefficient_three_rejection':'Attributed supplied logical inconsistency certificate; not replayed by this machine-startup checker.','ray_certificate':'On 0, self-loop writes behind the head while moving into the full blank half-line.','runs':details}
    if args.receipt:args.receipt.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='runs'},indent=2))

if __name__=='__main__':main()
