#!/usr/bin/env python3
"""Complete finite-window helper search with two predecessor bits."""
from extended_helpers import *

def context_sets(tree,index,width=2):
    raw=c.raw_nodes();prefixes=[]
    def find(t,p):
        if t=='x67':prefixes.append(p);return
        if isinstance(t,str):find(raw[t],p)
        elif c.isnode(t):find(t[0],p+(0,));find(t[1],p+(1,))
    find('node172',());assert len(prefixes)==1
    cs=defaultdict(set)
    def visit(t,p):
        if t in c.MACROS:return
        if c.isnode(t):
            cs[index[t]].add(p[-width:]);visit(t[0],p+(0,));visit(t[1],p+(1,))
    visit(tree,prefixes[0]);return cs

def localvalid_context(rows,folded,alias,chosen,contexts,width):
    for a,b,acts in chosen:
        for src in (a,b):
            for pre in contexts[src]:
                for v in (0,1):
                    w,d,z=rows[src,v];z=alias.get(z,z);dest=1 if d else -1
                    expect={i-width:x for i,x in enumerate(pre)};expect[0]=w
                    tape={i-width:x for i,x in enumerate(pre)};tape[0]=v
                    head=0;q=b;seen=set()
                    while True:
                        if q==z and head==dest and tape==expect:break
                        if head not in tape:return False
                        key=q,head,tuple(tape[i]for i in range(-width,1))
                        if key in seen:return False
                        seen.add(key)
                        if(q,tape[head])not in folded:return False
                        w,d,q=folded[q,tape[head]];tape[head]=w;head+=1 if d else -1
    return True

def window_ops(rows,shape,contexts,width=2):
    allctx=list(itertools.product((0,1),repeat=width));ids={p:i for i,p in enumerate(allctx)}
    required_masks=set()
    for a,b in itertools.combinations(sorted(shape),2):
        if not contexts[a]&contexts[b]:
            required_masks.add(tuple(sorted(ids[p]for p in contexts[a]|contexts[b])))
    bymask=[defaultdict(lambda:defaultdict(list)),defaultdict(lambda:defaultdict(list))]
    count=0;maxsteps=0
    for h in sorted({q for q,b in rows}):
        for v in (0,1):
            for firstwrite in (0,1):
                results={};uses={};durations={}
                for k,pre in enumerate(allctx):
                    tape={i-width:x for i,x in enumerate(pre)};expect=dict(tape);expect[0]=v;tape[0]=firstwrite
                    head=-1;q=h;seen=set();used=set();n=0
                    while head in tape and(q,tape[head])in rows:
                        key=q,head,tuple(tape[i]for i in range(-width,1))
                        if key in seen:break
                        seen.add(key);used.add(q);w,d,q=rows[q,tape[head]];tape[head]=w;head+=1 if d else -1;n+=1
                    if head==1 and tape==expect:results[k]=q;uses[k]=used;durations[k]=n+1
                for active in required_masks:
                    if any(k not in results for k in active):continue
                    signature=tuple(results[k]for k in active)
                    used=set().union(*(uses[k]for k in active));length=max(durations[k]for k in active)
                    bymask[v][active][signature].append(((firstwrite,False,h),used,length));count+=1;maxsteps=max(maxsteps,length)
    ops=[];extended_options=0
    for a,b in itertools.combinations(sorted(shape),2):
        opts=[];ca,cb=contexts[a],contexts[b]
        for v in (0,1):
            aa,bb=rows[a,v],rows[b,v]
            if aa==bb:opts.append([aa]);continue
            if ca&cb or aa[:2]!=(v,True) or bb[:2]!=(v,True):opts.append([]);continue
            active=tuple(sorted(ids[p]for p in ca|cb))
            signature=tuple(aa[2]if allctx[k]in ca else bb[2]for k in active)
            choices=[]
            for act,used,length in bymask[v][active].get(signature,[]):
                if not{a,b}&used:
                    choices.append(act)
                    if length>3 or act[0]!=v:extended_options+=1
            opts.append(choices)
        if all(opts):ops.append((a,b,opts))
    return ops,{'provider_entries':count,'longest_provider':maxsteps,'extended_options':extended_options}

def choose_context(rows,ops,contexts,width,target):
    variants=[[(a,b,tuple(acts))for acts in itertools.product(*choices)]for a,b,choices in ops]
    best=[];chosen=[]
    def search(i,used):
        nonlocal best
        if len(chosen)>len(best):
            folded,alias=apply(rows,chosen)
            if localvalid_context(rows,folded,alias,chosen,contexts,width):best=list(chosen)
            if len(best)>=target:return True
        if i==len(ops)or len(chosen)+len(ops)-i<=len(best):return False
        a,b,_=ops[i]
        if not used&{a,b}:
            for x in variants[i]:
                chosen.append(x);ans=search(i+1,used|{a,b});chosen.pop()
                if ans:return True
        return search(i+1,used)
    search(0,set());return best

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--width',type=int,default=2);ap.add_argument('--limit',type=int,default=0);ap.add_argument('--out',type=Path,default=ROOT/'research/context_helpers');a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True)
    start=time.monotonic();receipts=[]
    files=[SUPPORT/'verified196.grammar.json',SUPPORT/'separate196.grammar.json',SUPPORT/'scanner_6.grammar.json']+sorted((SUPPORT/'ties').glob('*.grammar.json'))
    if a.limit:files=files[:a.limit]
    for i,p in enumerate(files):
        t=c.read_grammar(p);rows,index,shape=c.build(t);contexts=context_sets(t,index,a.width);ops,meta=window_ops(rows,shape,contexts,a.width)
        chosen=choose_context(rows,ops,contexts,a.width,len(shape)-61);cost=len(shape)-len(chosen)
        rec={'grammar':p.name,'width':a.width,'nodes':len(shape),'candidate_pairs':len(ops),'compatible_folds':len(chosen),'effective_AX_cost':cost,**meta};receipts.append(rec);print(rec,flush=True)
        if cost<=61:
            folded,alias=apply(rows,chosen);ss,ins,cs=c.source(t);val=c.validate(folded,cs);print({'VALIDATION':val},flush=True)
            (a.out/f'candidate{i}.validation.json').write_text(json.dumps(val,indent=2)+'\n')
            if val['ok']:
                (a.out/f'candidate{134+cost}.grammar.json').write_text(p.read_text());(a.out/f'candidate{134+cost}.folds.json').write_text(json.dumps(chosen,indent=2)+'\n')
                (a.out/f'candidate{134+cost}.native.tm').write_text(''.join(f'{q} {b} {w} {"R"if d else"L"} {z}\n'for(q,b),(w,d,z)in sorted(folded.items())))
                break
    (a.out/'receipt.json').write_text(json.dumps({'width':a.width,'grammars':receipts,'elapsed_seconds':time.monotonic()-start},indent=2)+'\n')

if __name__=='__main__':main()
