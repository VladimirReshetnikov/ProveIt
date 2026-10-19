#!/usr/bin/env python3
"""Search two further global rotations through grammars of at most202 pairs.

Final acceptance compares every guarded successor to the original source;
intermediate grammars need not be executable-equivalent. Counts are source
pair subtrees and do not charge binary helpers or initialization.
"""
import json
import time
import rotation_search as r

def main():
    began=time.monotonic();raw=r.a.PROGRAM.read_bytes()
    ls,cases,by,first=r.a.read_program(raw)
    original=r.load(raw);base=r.rotate(original,95,'left')
    assert r.check(base,ls,cases,set())['unique_pairs']==202
    first_layer={}
    for p in r.reachable(base):
        for direction in ('left','right'):
            c=r.rotate(base,p,direction)
            if c is None or c==base:continue
            size=len(r.reachable(c))
            if size<=202:first_layer.setdefault(c,{'pivot':p,'direction':direction,'size':size})
    print(json.dumps({'first_layer_candidates':len(first_layer),'interned_entries':len(r.entries)}),flush=True)
    finals={};tested=0;success=[]
    for index,(state,first_move) in enumerate(first_layer.items()):
        for p in r.reachable(state):
            for direction in ('left','right'):
                c=r.rotate(state,p,direction)
                if c is None or c==state:continue
                size=len(r.reachable(c))
                if size>=202 or c in finals:continue
                finals[c]=[first_move,{'pivot':p,'direction':direction,'size':size}]
                result=r.check(c,ls,cases,set());tested+=1
                if result is None:continue
                result['moves']=finals[c];success.append(result)
                r.dump_graph(c,r.OUT/f'rotation_plateau_success_{len(success):02}.json',result)
                print(json.dumps({'found':result,'seconds':time.monotonic()-began}),flush=True)
        if (index+1)%20==0:
            print(json.dumps({'first_layers_processed':index+1,'finals_tested':tested,'successful':len(success),'seconds':time.monotonic()-began}),flush=True)
    result={'first_layer_candidates':len(first_layer),'candidate_final_count':len(finals),
            'all_guard_checks':tested,'successes':success,'seconds':time.monotonic()-began}
    (r.OUT/'rotation_plateau_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':main()
