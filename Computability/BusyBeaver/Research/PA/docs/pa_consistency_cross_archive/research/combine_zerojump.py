#!/usr/bin/env python3
"""Cross-compose the source26 zero-decrement optimization as a separate trial."""
import combine_recent as x
import joint_readers as jr
import json
x.combined[27,1]=(1,True,21)
p,op,arg=x.outside[26]
assert (op,arg)==('breakTo',1)
x.outside[26]=(p,'dec',6)
out=x.ROOT/'research/cross_zerojump';out.mkdir(parents=True,exist_ok=True)
receipts=[]
for i,nm in enumerate(('diagonal196','separate196')):
    t=x.c.read_grammar(x.AX/nm/'grammar.json');r,idx,sh=x.c.build(t)
    ch=x.s.bestcompatible_all(r,sh);rr,ali=x.s.apply(r,ch)
    ss,ins,cs=x.c.source(t);check=x.c.validate(rr,cs);st=x.startup(rr,ss)
    rec={'name':nm,'states':len(rr)//2,'source_sites':len(ss),'contracts':check,'startup':st}
    x.export(out/nm,t,rr,ch,ss,rec);receipts.append(rec);print(json.dumps(rec),flush=True)
    # Joint zero/positive invariant from exact clean seed. Positive decrement
    # admits both zero and nonzero remainder; all transitions are checked.
    seen={(25,1)};todo=list(seen)
    def succ(pc,m):
        z=ins[pc]
        if z[0]=='jump':return [(z[1],m)]
        if z[0]=='inc':return [(z[2],m|(1<<z[1]))]
        if z[0]=='dec':
            bit=1<<z[1]
            return [(z[3],m&~bit),(z[3],m)] if m&bit else [(z[2],m)]
        return []
    for pc,m in todo:
        for nxt in succ(pc,m):
            if nxt not in seen:seen.add(nxt);todo.append(nxt)
    valid=all(nxt in seen for pc,m in seen for nxt in succ(pc,m))
    masks=sorted(m for pc,m in seen if pc==26)
    inv={'pairs':len(seen),'closed':valid,'site26_masks':masks,'register6_zero':bool(masks)and all(m&64==0 for m in masks)}
    rec['invariant']=inv;print(json.dumps(inv),flush=True)
    (out/nm/'invariant.json').write_text(json.dumps(inv,indent=2)+'\n')
    (out/nm/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
rs=[]
files=[x.AX/'diagonal196/grammar.json',x.AX/'separate196/grammar.json']+sorted((x.AX/'search/ties').glob('*.json'))+[x.AX/'search/scanner_6.grammar.json']
for i,f in enumerate(files):
    r=jr.screen(f);rs.append(r)
    if r.get('trials'):print(json.dumps(r),flush=True)
(out/'summary.json').write_text(json.dumps({'candidates':receipts,'joint_reader_grammars':len(rs),'results':rs},indent=2)+'\n')
print('FINISHED',len(rs),'joint-reader layouts',flush=True)
