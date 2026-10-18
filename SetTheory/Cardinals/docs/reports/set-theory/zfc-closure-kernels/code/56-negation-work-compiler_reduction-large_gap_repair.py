#!/usr/bin/env python3
"""Measure conservative context repair at an explicitly larger frame gap.

The affine audit covers all gap+n, n>=0, but no startup or source-equivalence
claim follows automatically from passing this experiment.
"""
from __future__ import annotations
import argparse,json,sys,time
from pathlib import Path
import search_structural as s
import gap_diagnostic as g
sys.path.insert(0,str(s.HERE.parent))
import context_repair as c

def main():
    ap=argparse.ArgumentParser();ap.add_argument('input',type=Path)
    ap.add_argument('--output',type=Path,required=True);ap.add_argument('--shorten',action='store_true')
    ap.add_argument('--boot',action='store_true');ap.add_argument('--gap',type=int)
    a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True)
    d=json.loads(a.input.read_text());nodes={int(k):tuple(map(tuple,v)) for k,v in d['nodes'].items()};root=d['root']
    gap=a.gap or max(40,max(len(p) for p,e in s.sites(nodes,root))+6)
    forced=set();history=[];begun=time.monotonic()
    for it in range(len(nodes)+1):
        table,entries,changed,old=c.emit(nodes,root,forced)
        if a.shorten:
            table={(q,b):(w,m,84 if t==74 else t) for (q,b),(w,m,t) in table.items() if q!=74}
        runtime,used=g.check_gap(table,nodes,root,gap)
        result=dict(iteration=it,forced=sorted(forced),changed_nodes=len(changed),runtime=runtime,
                    runtime_states=len({q for q,b in used|s.audit.BOX_PAIRS}))
        print('ITERATION',it,len(changed),result['runtime_states'],runtime,flush=True)
        history.append(result)
        if runtime['passed']:
            pruned=s.prune(table,used);result['contract_only_states']=len(pruned)//2
            (a.output/'contract_only.tm').write_bytes(s.audit.encode(pruned))
            if a.boot:
                boot,bu=g.safe_boot(table,gap)
                result['boot']=boot
                if boot['outcome']=='sufficient_truth_root':
                    pt=s.prune(table,used|bu);result['working_states']=len(pt)//2
                    (a.output/'runtime_and_later_root.tm').write_bytes(s.audit.encode(pt))
            break
        p=runtime['failure']['path'];path=c.pathnodes(nodes,root,p)
        choices=[n for n in path if n not in changed and s.NODE_LABELS[old[n]] not in s.PURE]
        if not choices:choices=[n for n in path if n not in changed]
        if not choices:
            result['unrepaired_failure']=True;break
        forced.add(choices[0])
    out=dict(input=str(a.input),gap=gap,shortened=a.shorten,history=history,elapsed=time.monotonic()-begun)
    (a.output/'results.json').write_text(json.dumps(out,indent=2)+'\n')
    print('DONE',result,flush=True)

if __name__=='__main__':main()
