#!/usr/bin/env python3
"""Search semantics-preserving decoder rotations with the exact253 boot protected.

This is an experimental affine audit, not a kernel proof or minimality result.
Input semantics and the published box contracts are independently pinned.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import hashlib,json,time,sys
import rotate_search as rot
import prior_context_search as ctx
from analyze_table import parse_table

HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'upstream253/ZF/m254'
OLD=json.loads((HERE/'decoder_entries.json').read_text())
NODES={int(k):tuple(map(tuple,v)) for k,v in OLD['nodes'].items()}
ROOT=OLD['root']
PHYS=(6,7,0,2,1,8,4,3,5)
BOX_STATES={0,1,2,3,4,6,28,31,38,40,43,44,48,56,59,60,63,64,69,73,75,83,85,95,97,109,112,131}
BOX_PAIRS={(str(q),b) for q in BOX_STATES for b in (0,1)}-{('3',0)}
base_rows,*_=parse_table(BASE/'machine/zfc_254.tm')
BASE253={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in base_rows.items() if q!=8}
BASE253.update({('3',0):(0,'L','48'),('5',0):(1,'R','97'),('5',1):(1,'R','64'),('49',1):(0,'R','5')})

def boot_reference():
    q,h,tape='5',0,set();used=set()
    for _ in range(312975):
        key=q,int(h in tape);used.add(key)
        w,d,q=BASE253[key]
        if w:tape.add(h)
        else:tape.discard(h)
        h+=1 if d=='R' else -1
    assert q=='96' and h==-17
    return used,{'state':q,'head':h,'ones':sorted(tape)}

BOOT_USED,BOOT_END=boot_reference()
OLD_FP={v:int(n) for n,v in OLD['fingerprints'].items()}
CONTROL_OPTIONS={}
for n,pair in NODES.items():
    for bit,e in enumerate(pair):
        if e[0] not in 'BC':continue
        key=e,bit
        counts=CONTROL_OPTIONS.setdefault(key,Counter())
        for state,weight in OLD['state_entries'][str(n)].items():
            counts[BASE253[state,bit]]+=weight

def emit(nodes,root):
    @lru_cache(None)
    def fingerprint(edge):
        if edge[0]=='N':
            a,b=nodes[edge[1]]
            text='N('+fingerprint(a)+','+fingerprint(b)+')'
        else:text=':'.join(map(str,edge))
        return hashlib.sha256(text.encode()).hexdigest()
    table=BASE253.copy();entries={};allocate=255
    def modal(counts):return max(counts,key=counts.get)
    for n in nodes:
        f=fingerprint(('N',n))
        if n==root:entries[n]='96'
        elif f in OLD_FP:entries[n]=modal(OLD['state_entries'][str(OLD_FP[f])])
        else:entries[n]=str(allocate);allocate+=1
    def transition(edge,bit):
        if edge[0]=='N':return bit,'R',entries[edge[1]]
        if edge[0]=='B' and edge[1]==1:return 0,'L','7' if bit==0 else '33'
        if edge[0] in 'BC':return CONTROL_OPTIONS[edge,bit].most_common(1)[0][0]
        return bit,'R',modal(OLD['leaf_entries'][':'.join(map(str,edge))])
    for n in nodes:
        if entries[n]=='96' or fingerprint(('N',n)) not in OLD_FP:
            for bit,edge in enumerate(nodes[n]):table[entries[n],bit]=transition(edge,bit)
    return table

def sites(nodes,root):
    output=[];todo=[(('N',root),'')]
    while todo:
        e,p=todo.pop();k=e[0]
        if k=='N':
            a,b=nodes[e[1]];todo.extend([(b,p+'1'),(a,p+'0')])
        else:output.append((p,'C'+k,None if k=='H' else PHYS[e[1]] if k in 'ID' else e[1]))
    return output

class Tracking(dict):
    def __init__(self,x):super().__init__(x);self.used=set()
    def __getitem__(self,k):self.used.add(k);return super().__getitem__(k)

def rm_prefix(nodes,root,limit=2000):
    import prior_rm_verify as rm
    regs=[2]+[0]*8;pc='';out={}
    for k in range(limit+1):
        out.setdefault((pc.rstrip('0'),tuple(regs)),k)
        op,full=rm.site(nodes,root,pc)
        if op[0]=='H':break
        positive=op[0]=='D' and regs[op[1]]>0
        if op[0]=='I':regs[op[1]]+=1
        if positive:regs[op[1]]-=1
        pc=rm.nextpc(op,full,positive)
    return out

def frame(tape,h,depth):
    if h-1 not in tape or any(p<h-1 for p in tape):return None
    headers=[p-h for p in tape if p-h>=depth]
    if not headers:return None
    gap=min(headers)
    if gap<40:return None
    pc=''.join('1' if h+i in tape else '0' for i in range(depth)).rstrip('0')
    x=h+gap+1;regs=[]
    while x not in tape and x+1 in tape:
        x+=1;n=0
        while x in tape:n+=1;x+=1
        regs.append(n-1)
    if len(regs)<9 or any(p>=x for p in tape):return None
    source=[0]*9
    for physical,index in enumerate((2,4,3,7,6,8,0,1,5)):source[index]=regs[physical]
    return pc,tuple(source),gap,regs

def boot_candidate(table,nodes,root,fuel=750000):
    prefix=rm_prefix(nodes,root);depth=rot.zero_metrics(nodes,root)[2]
    q,h,tape='5',0,set();used=set();dispatches=0
    for t in range(fuel+1):
        if q=='96':
            dispatches+=1;f=frame(tape,h,depth)
            if f is not None and f[:2] in prefix:
                return {'outcome':'matched','steps':t,'rm_prefix_steps':prefix[f[:2]],
                        'head':h,'state':q,'pc':f[0],'source_registers':list(f[1]),
                        'gap':f[2],'spare_blocks':len(f[3])-9,
                        'spare_nonzero':[(i,v) for i,v in enumerate(f[3][9:]) if v],
                        'ones':sorted(tape),'dispatches':dispatches},used
        if t==fuel:break
        key=q,int(h in tape);used.add(key)
        if key not in table:return {'outcome':'halt','steps':t},used
        w,d,q=table[key]
        if w:tape.add(h)
        else:tape.discard(h)
        h+=1 if d=='R' else -1
    return {'outcome':'fuel_limit','steps':fuel,'dispatches':dispatches},used

def evaluate(nodes,root):
    try:table=emit(nodes,root)
    except KeyError as ex:return {'outcome':'unsupported_exposed_leaf','leaf':str(ex)}
    assert all(table[p]==BASE253[p] for p in BOX_PAIRS)
    ns=ctx.executor(table,BASE/'tools/tm/symexec.py')
    cs=ctx.cases(ns,sites(nodes,root));tracked=Tracking(table);ns['T']=tracked
    for i,c in enumerate(cs):
        if not ctx.check(ns,c):return {'outcome':'affine_failure','case':i,'path':c[1],'branch':c[4]}
    boot,boot_used=boot_candidate(table,nodes,root)
    if boot['outcome']!='matched':return {'outcome':'boot_'+boot['outcome'],'boot':boot,'affine_cases':len(cs)}
    used=tracked.used|boot_used|BOX_PAIRS
    retained={q for q,b in used}|{'96','5'}
    pruned={}
    for (q,b),(w,d,t) in table.items():
        if q not in retained:continue
        if t not in retained|{'254'}:
            assert (q,b) not in used
            t='5'
        pruned[q,b]=w,d,t
    assert len(pruned)==2*len(retained)
    return {'outcome':'passed','working_states':len(retained),'branch_cases':len(cs),
            'decoder_nodes':len(nodes),'depth':rot.zero_metrics(nodes,root)[2],
            'boot':boot,
            'new_rows_before_pruning':len(table)//2-len(BASE253)//2,
            'pruned_working_states':len(table)//2-len(retained),'table':pruned}

def emit_table(path,table):
    path.write_text('#! start 5\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(table.items(),key=lambda v:(int(v[0][0]),v[0][1]))))

def main():
    begin=time.monotonic();results=[];counts=Counter();best=253
    out=HERE/'results';out.mkdir(exist_ok=True)
    baseline=evaluate(NODES,ROOT);assert baseline['outcome']=='passed' and baseline['working_states']==253
    options=rot.options(NODES)
    for index,(n,e,kind) in enumerate(options):
        nodes,root=rot.mutate(NODES,ROOT,n,e);zero=rot.zero_metrics(nodes,root)
        if zero[1]>7 or zero[2]>39:result={'outcome':'shape_bound'}
        else:result=evaluate(nodes,root)
        table=result.pop('table',None);result.update(index=index,node=n,operation=kind)
        results.append(result);counts[result['outcome']]+=1
        if result['outcome']=='passed' and result['working_states']<best:
            best=result['working_states'];print('best',best,'option',index,n,kind,flush=True)
            (out/'best_dag.json').write_text(json.dumps({'root':root,'nodes':nodes},indent=2)+'\n')
            emit_table(out/'best.tm',table)
        if (index+1)%20==0:
            print('done',index+1,'/',len(options),dict(counts),'elapsed',round(time.monotonic()-begin,1),flush=True)
            (out/'single_rotation_results.json').write_text(json.dumps({'scope':'All 238 single closed-sequence reassociations from the 203-node baseline; affine audit and finite boot matching up to2000 RM steps,750000 TM steps; fixed published box contracts. No kernel verification.', 'counts':counts,'best_states':best,'results':results},indent=2)+'\n')
    report={'scope':'All single closed-sequence reassociations or increment commutations generated by source09 options from the 203-node baseline; affine audit and finite bootstrap matching within2000 RM steps and750000 TM steps, with unchanged published box contracts. No kernel verification; no semantic minimality claim.',
            'options':len(options),'baseline_states':253,'counts':counts,'best_states':best,
            'boot_steps':312975,'protected_boot_pairs':len(BOOT_USED),'protected_box_pairs':len(BOX_PAIRS),
            'elapsed_seconds':round(time.monotonic()-begin,3),'results':results}
    (out/'single_rotation_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='results'},indent=2),flush=True)

if __name__=='__main__':main()

