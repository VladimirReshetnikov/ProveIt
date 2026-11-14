#!/usr/bin/env python3
"""Reproduce the selected 196-state padding-detour machine; standard library only.

The symbolic check uses the unchanged imported register-engine interfaces.
This is an executable certificate, not an end-to-end Lean proof.
"""
from pathlib import Path
import sys,json,hashlib
P=Path(__file__).resolve().parent
sys.path[:0]=[str(P/'code'),str(P/'code/search')]
import compiler as c
import support
from source_checks import source_binding
from verify_emitter import audit,word,require


def read_table(path):
    out={}
    for line in path.read_text().splitlines():
        q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
        require((q,b)not in out,'duplicate transition')
        require(b in(0,1)and w in(0,1)and d in('L','R'),'binary transition')
        out[q,b]=(w,d=='R',n)
    return out


def main():
    if not __debug__:
        raise SystemExit('Run without python -O; parser assertions are required.')
    d=P/'selected196'
    t=c.read_grammar(d/'grammar.json')
    raw,index,shape=c.build(t)
    closing=[]
    for q,node in shape.items():
        for bit,child in enumerate(node):
            if child==c.BREAK:
                require(bit==1,'rightmost closing address bit')
                raw[q,bit]=(1,True,113);closing.append((q,bit))
    require(len(closing)==1,'one final closing reader row')
    folds=json.loads((d/'folds.json').read_text())
    require(len({q for a,b,acts in folds for q in(a,b)})==2*len(folds),'disjoint folds')
    folded,aliases=support.apply(raw,folds)
    require(support.localvalid(raw,folded,aliases,folds),'compatible contextual reader folds')
    require(folded==read_table(d/'machine.native.tm'),'exact native table')
    labels=json.loads((d/'labels.json').read_text())
    require(labels[0]==74 and labels[-1]==254,'start and halt relabelling')
    require(len(set(labels))==len(labels),'injective relabelling')
    dense=read_table(d/'machine.tm');count=len(labels)-1
    require(count==196,'196 working states')
    require(set(dense)=={(q,b)for q in range(count)for b in(0,1)},'total binary table')
    require({(labels[q],b):(w,direction,labels[n])for(q,b),(w,direction,n)in dense.items()}==folded,'dense table equality')
    original,_=c.machine()
    require(all(folded[q,b]==original[q,b]for q in c.BOXSTATES for b in(0,1)),'unchanged protected register engine')
    for q,b in[(113,0),(302,1)]:
        require(folded[q,b]==original[q,b],'unchanged closing detour rows')
    baseline=c.read_grammar(P/'code/separate196/grammar.json')
    require(word(t)==word(baseline),'exact separate-head 190-token source word')
    emission=audit('separate196')
    sites,ins,contracts=c.source(t)
    binding=source_binding(t,sites,ins)
    # The last AX leaf follows a nonempty suffix of right edges; padding is
    # explicit in its frame.  Unlike zero-CD closings, no branch restriction
    # is needed here.
    prefix=(1,0,1,0,1,0,0,1);path=prefix;x=t
    while c.isnode(x):path+=(1,);x=x[1]
    require(x==c.BREAK and path[-2:]==(1,1),'closing address ends in 11')
    require(48-len(path)>=1,'following padding bit is zero for every gap parameter')
    rawcheck=c.validate(raw,contracts)
    require(rawcheck['ok'],'all raw whole-register-file contracts')
    foldedcheck=c.validate(folded,contracts)
    require(foldedcheck['ok'],'all folded whole-register-file contracts')
    q=0;head=0;ones=set()
    for _ in range(58154):
        w,direction,q=dense[q,int(head in ones)]
        (ones.add if w else ones.discard)(head);head+=1 if direction else-1
    values=[0,0,0,0,0,0,2,0,0]+[1]*26
    target={head-1,head};pos=head+48;target.add(pos);pos+=1
    for value in values:
        pos+=1;target.update(range(pos,pos+value+1));pos+=value+1
    require((labels[q],head)==(84,-2)and ones==target,'exact complete blank startup')
    reached={0};todo=[0]
    while todo:
        q=todo.pop()
        for b in(0,1):
            n=dense[q,b][2]
            if n<count and n not in reached:reached.add(n);todo.append(n)
    require(reached==set(range(count)),'all working states graph-reachable')
    receipt={'working_states':count,'rows':len(dense),'grammar_reader_states':len(shape),'simultaneous_folds':len(folds),'source_sites':len(sites),'emitter':emission,'source_binding':binding,'closing_action':'native 1 R113','closing_row_before_folding':closing,'closing_path_length':len(path),'unconditional_closing':True,'raw_contracts':rawcheck,'folded_contracts':foldedcheck,'protected_register_engine_unchanged':True,'startup_literal_steps':58154,'complete_startup_exact':True,'graph_reachable_states':len(reached),'machine_sha256':hashlib.sha256((d/'machine.tm').read_bytes()).hexdigest(),'end_to_end_Lean_kernel_checked':False}
    (P/'reproduced_r113196.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
