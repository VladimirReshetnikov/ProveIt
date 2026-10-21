#!/usr/bin/env python3
"""Replay the finite counterexample/positive control, optionally all searches."""
from pathlib import Path
import argparse,json,hashlib,subprocess,sys
import search_two_branch_folds as folds
import search_two_branch_walks as walks
import verify_rejected_52_154 as rejected
ROOT=Path(__file__).resolve().parents[1]
def need(p,m):
    if not p:raise ValueError(m)
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--full-search',action='store_true');ap.add_argument('--context-search',action='store_true');a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=False)
    index=json.loads((ROOT/'inputs/source-index.json').read_text())
    for x in index['tables']+[index['source_sites']]:need(hashlib.sha256((ROOT/'inputs'/x['file']).read_bytes()).hexdigest()==x['sha256'],'input hash: '+x['file'])
    counter=rejected.verify();dump(a.output/'counterexample.json',counter)
    positive=a.output/'positive';positive.mkdir();r=folds.search(ROOT/'research/synthetic216-positive-control.tm',3,positive)
    want=[s for s in r['solutions']if s['keep']==69 and s['drop']==400 and [tuple(b['action'])for b in s['branches']]==[(0,-1,213),(1,-1,213)]]
    need(bool(want),'nontrivial both-branch positive control absent')
    # Independent replay uses the literal fixture and accepted generated rows.
    T,_,_,_=folds.parse(ROOT/'research/synthetic216-positive-control.tm');N,_,_,_=folds.parse(positive/f"candidate_{r['solutions'].index(want[0]):03d}.native.tm")
    for old,m in((69,0),(400,1)):
        for bit in(0,1):
            tape={-1:m,0:bit};before=tape.copy();q,h=69,0
            for _ in range(3):
                need(h in tape,'positive read outside known tape');v,d,z=N[q,tape[h]];tape[h]=v;q,h=z,h+d
            need((q,h,tape)==(T[old,bit][2],1,before),'positive endpoint differs')
    dump(a.output/'positive-control.json',{'status':'PASS','exact_solution':want[0],'four_literal_blocks_checked':True})
    report={'input_tables':len(index['tables']),'counterexample':'PASS','positive_control':'PASS','full_search':False,'context_search':False}
    if a.full_search:
        three=json.loads((ROOT/'evidence/two-branch-corpus.json').read_text());long=json.loads((ROOT/'evidence/two-branch-walk-corpus.json').read_text());oldthree={x['name']:x for x in three['tables']};oldlong={x['name']:x for x in long['tables']}
        results=[]
        for x in index['tables']:
            path=ROOT/'inputs'/x['file'];o=a.output/x['name'];o.mkdir();o3=o/'three';o3.mkdir();o5=o/'walks';o5.mkdir()
            r3=folds.search(path,3,o3);r5=walks.search(path,o5,5,64)
            for key in('pair_retention_choices','both_target_branches_differ','branch_pass','solutions','window_count'):need(r3[key]==oldthree[x['name']][key],'three-step discrepancy '+x['name']+' '+key)
            for key in('pair_retention_choices','both_literal_target_branches_differ','branch_pass','solutions','window_count','profile_results'):need(r5[key]==oldlong[x['name']][key],'walk discrepancy '+x['name']+' '+key)
            dump(o3/'result.json',r3);results.append({'name':x['name'],'three':'MATCH','walks':'MATCH'});print(x['name'],'MATCH',flush=True)
        report['full_search']=results
    if a.context_search:
        V=ROOT/'vendor';out=a.output/'context-fusion'
        cmd=[sys.executable,'-B',str(V/'search_contextual_fusions.py'),'--table',str(ROOT/'inputs/context.tm'),'--sites',str(ROOT/'inputs/sites215.json'),'--engine',str(ROOT/'inputs/engine-context.json'),'--mapping',str(ROOT/'inputs/legacy_mapping.json'),'--witnesses',str(ROOT/'inputs/engine_row_witnesses.json'),'--support-dir',str(V/'support'),'--runtime-dir',str(V/'runtime'),'--output',str(out)]
        subprocess.run(cmd,check=True);r=json.loads((out/'receipt.json').read_text())
        need((r['specifications'],r['prefix_pass'],r['delivery_class_pass'],r['rejected'],r['unaccepted_survivors'])==(3143,1435,480,480,0),'context-search receipt differs')
        report['context_search']='MATCH'
    dump(a.output/'verification.json',report);print(json.dumps(report,indent=2))
if __name__=='__main__':main()
