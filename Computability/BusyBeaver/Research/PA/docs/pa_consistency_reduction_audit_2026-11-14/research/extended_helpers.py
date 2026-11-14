#!/usr/bin/env python3
"""Search exact two-cell helper computations beyond the three-step motif.

The helper is forbidden to read outside the predecessor/current two-cell
window. Each prospective simultaneous quotient is independently replayed on
all four local contexts, then eligible tables receive whole-macro validation.
"""
from emitter_search import *
from support import localvalid,bestcompatible,apply
from collections import defaultdict
import itertools

def general_ops(rows,shape):
    incoming=defaultdict(set)
    for(q,b),(w,d,z)in rows.items():
        if d and w==b and z in shape:incoming[z].add(b)
    left=[q for q in shape if incoming[q]=={0}];right=[q for q in shape if incoming[q]=={1}]
    providers=[defaultdict(list),defaultdict(list)]
    for h in sorted({q for q,b in rows}):
        for v in (0,1):
            for firstwrite in (0,1):
                results=[];used=set();durations=[]
                for p in (0,1):
                    tape={-1:p,0:firstwrite};q=h;head=-1;seen=set();n=0
                    while head in tape and(q,tape[head])in rows:
                        key=q,head,tape[-1],tape[0]
                        if key in seen:break
                        seen.add(key);used.add(q)
                        w,d,q=rows[q,tape[head]];tape[head]=w;head+=1 if d else -1;n+=1
                    if head==1 and tape=={-1:p,0:v}:results.append(q);durations.append(n+1)
                    else:break
                if len(results)==2:
                    providers[v][tuple(results)].append(((firstwrite,False,h),used,max(durations)))
    out=[];extended=0;longest=0
    for a in left:
        for b in right:
            opts=[]
            for v in (0,1):
                acta,actb=rows[a,v],rows[b,v]
                if acta==actb:opts.append([acta]);continue
                if acta[:2]!=(v,True) or actb[:2]!=(v,True):opts.append([]);continue
                values=[]
                for act,used,length in providers[v].get((acta[2],actb[2]),[]):
                    if not {a,b}&used:
                        values.append(act);longest=max(longest,length)
                        if length>3 or act[0]!=v:extended+=1
                opts.append(values)
            if all(opts):out.append((a,b,opts))
    return out,{'extended_options':extended,'maximum_helper_steps':longest,
                'provider_signatures':[len(x)for x in providers]}

def choose(rows,ops):
    bound=len(c.max_matching(ops));best=[]
    variants=[[(a,b,tuple(acts))for acts in itertools.product(*choices)] for a,b,choices in ops]
    # Demand the exact simultaneous quotient, including modified helper rows.
    for size in range(bound,0,-1):
        chosen=[]
        def search(i,used):
            if len(chosen)==size:
                folded,alias=apply(rows,chosen)
                return list(chosen) if localvalid(rows,folded,alias,chosen) else None
            if i==len(ops)or len(chosen)+len(ops)-i<size:return None
            a,b,_=ops[i]
            if not used&{a,b}:
                for x in variants[i]:
                    chosen.append(x);ans=search(i+1,used|{a,b});chosen.pop()
                    if ans is not None:return ans
            return search(i+1,used)
        ans=search(0,set())
        if ans is not None:return ans
    return []

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,default=ROOT/'research/extended_helpers');args=ap.parse_args()
    args.out.mkdir(parents=True,exist_ok=True);start=time.monotonic();receipts=[]
    files=[SUPPORT/'verified196.grammar.json',SUPPORT/'separate196.grammar.json',SUPPORT/'scanner_6.grammar.json']+sorted((SUPPORT/'ties').glob('*.grammar.json'))
    for i,p in enumerate(files):
        t=c.read_grammar(p);rows,index,shape=c.build(t);oldops=c.opportunities_fast(rows,shape)
        ops,meta=general_ops(rows,shape);chosen=choose(rows,ops);cost=len(shape)-len(chosen)
        rec={'grammar':p.name,'sha256':__import__('hashlib').sha256(p.read_bytes()).hexdigest(),'nodes':len(shape),'ordinary_pairs':len(oldops),'extended_pairs':len(ops),'folds':len(chosen),'effective_cost':cost,**meta};receipts.append(rec)
        print(rec,flush=True)
        if cost<=61:
            folded,alias=apply(rows,chosen);ss,ins,cs=c.source(t);val=c.validate(folded,cs);print({'VALIDATION':val},flush=True)
            (args.out/f'candidate{i}.validation.json').write_text(json.dumps(val,indent=2)+'\n')
            if val['ok']:
                (args.out/f'candidate{134+cost}.grammar.json').write_text(p.read_text());(args.out/f'candidate{134+cost}.folds.json').write_text(json.dumps(chosen,indent=2)+'\n')
                (args.out/f'candidate{134+cost}.native.tm').write_text(''.join(f'{q} {b} {w} {"R" if d else "L"} {z}\n'for(q,b),(w,d,z)in sorted(folded.items())))
                break
    (args.out/'receipt.json').write_text(json.dumps({'grammars':receipts,'elapsed_seconds':time.monotonic()-start,'scope':'all deterministic two-cell helpers until exit or repeated local configuration; no arbitrary-context guarantee or global lower bound'},indent=2)+'\n')

if __name__=='__main__':main()
