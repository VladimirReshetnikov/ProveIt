#!/usr/bin/env python3
"""Two-step plateau search preserving alias structure and inspected context."""
import argparse
import json
import time
import rotation_alias_descent as z
import grammar_stats as gs
r=z.r

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--start',default='rotation_alias7_candidate_16.json')
    parser.add_argument('--pairs',type=int,default=203)
    parser.add_argument('--prefix',default='rotation_alias_plateau')
    args=parser.parse_args();began=time.monotonic();raw=r.a.PROGRAM.read_bytes()
    ls,cases,by,first=r.a.read_program(raw);original=r.load(raw)
    fixed,contexts,_,_=z.setup(original)
    root=gs.import_graph(json.loads((z.HERE/args.start).read_text()))
    assert z.context_check(root,contexts)
    oldscore=gs.score(root);firsts={};checks=0;examined=0;seen=set();successes=[]
    for p in r.reachable(root):
        if p in fixed:continue
        for direction in ('left','right'):
            c=r.rotate(root,p,direction)
            if c is None:continue
            reach=r.reachable(c)
            if len(reach)>args.pairs+1 or not fixed.issubset(reach):continue
            if gs.stats(c)[4]>8:continue
            firsts[c]=[p,direction]
    print(json.dumps(dict(firsts=len(firsts),start_score=gs.stats(root)[5],pairs=args.pairs)),flush=True)
    for index,(f,move1) in enumerate(firsts.items()):
        for p in r.reachable(f):
            if p in fixed:continue
            for direction in ('left','right'):
                c=r.rotate(f,p,direction)
                if c is None or c in seen:continue
                seen.add(c);examined+=1
                if gs.stats(c)[4]>7 or gs.score(c)>=oldscore:continue
                reach=r.reachable(c)
                if len(reach)>args.pairs or not fixed.issubset(reach):continue
                if not z.context_check(c,contexts):continue
                answer=z.cr.repair(c,ls,cases,by,first);checks+=1
                if answer is None:continue
                final,meta=answer
                reach=r.reachable(final)
                if len(reach)>args.pairs or not fixed.issubset(reach) or not z.context_check(final,contexts):continue
                meta.update(moves=[move1,[p,direction]],histogram=gs.stats(final)[5],
                    protected_pairs=len(fixed),preserved_alias_context_occurrences=len(contexts))
                path=z.HERE/f'{args.prefix}_candidate_{len(successes):03}.json'
                r.dump_graph(final,path,meta);successes.append({k:v for k,v in meta.items() if k!='edits'})
                print(json.dumps(successes[-1]),flush=True)
                if len(gs.stats(final)[5])<=7:
                    print('GOAL CD trailing-zero bound six',str(path),flush=True)
                    break
            if successes and len(successes[-1]['histogram'])<=7:break
        if successes and len(successes[-1]['histogram'])<=7:break
    out=dict(seconds=time.monotonic()-began,examined=examined,checks=checks,successes=successes)
    (z.HERE/f'{args.prefix}_results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='successes'},indent=2),flush=True)

if __name__=='__main__':main()
