#!/usr/bin/env python3
"""Cross-graft the latest command and AX improvements; no success presumed."""
from pathlib import Path
import json, sys, hashlib, time, argparse
ROOT=Path(__file__).resolve().parents[1]
AX=ROOT/'inputs/axioms'
COM=ROOT/'inputs/combined'
sys.path.insert(0,str(AX/'search'))
import support as s
c=s.c
pair=(s.INC,s.INC);c.MACROS[pair]=99;c.MACROS[(pair,pair)]=190
baseline_machine=c.machine
base_source=c.source
old,labels=baseline_machine()
def read_dense(path):
    m={}
    for ln in path.read_text().splitlines():
        q,b,w,d,n=ln.split();m[int(q),int(b)]=int(w),d=='R',int(n)
    return m
combined_dense=read_dense(COM/'machines/h_only_mp_h.tm')
combined={(labels[q],b):(w,d,labels[n]) for(q,b),(w,d,n) in combined_dense.items()}
OLD_PREFIX=(1,0,1,0,1,0,0,1)
NEW_PREFIX=(1,0,0,1,0,1,0,0,1)
outside=[(tuple(p),op[0],op[1] if len(op)>1 else None) for p,op in json.loads((COM/'machines/h_only_mp_h_sites.json').read_text()) if tuple(p[:9])!=NEW_PREFIX]
assert len(outside)==145

def make_contracts(sites):
    bypath={p:i for i,(p,*_) in enumerate(sites)}
    def locate(p):
        if p in bypath:return bypath[p]
        for i,(q,*_) in enumerate(sites):
            if q[:len(p)]==p or (p[:len(q)]==q and not any(p[len(q):])):return i
        raise ValueError(p)
    def after(p):
        for i in range(len(p)-1,-1,-1):
            if p[i]==0:return locate(p[:i]+(1,))
        raise ValueError(p)
    def cut(p,b,k):
        for i in range(len(p)-1,-1,-1):
            if p[i]==b:
                k-=1
                if not k:return p[:i]
        raise ValueError((p,b,k))
    ins=[]
    for p,op,arg in sites:
        if op=='inc':i=('inc',arg,after(p))
        elif op=='dec':i=('dec',arg,after(cut(p,0,1)),after(p))
        elif op=='breakTo':i=('jump',after(cut(p,0,arg)))
        elif op=='continueTo':i=('jump',locate(cut(p,1,arg)))
        elif op=='halt':i=('halt',)
        else:raise ValueError(op)
        ins.append(i)
    cs=[]
    for i,code in enumerate(ins):
        st=c.frame(sites[i][0])
        if code[0]=='inc':
            _,r,n=code;cs.append((i,None,st,c.canonical(c.frame(sites[n][0],0,('x','inc',c.PHYSICAL[r])))))
        elif code[0]=='dec':
            _,r,z,p=code
            cs.append((i,(c.PHYSICAL[r],True),st,c.canonical(c.frame(sites[z][0]))))
            cs.append((i,(c.PHYSICAL[r],False),st,c.canonical(c.frame(sites[p][0],1,('x','dec',c.PHYSICAL[r])))))
        elif code[0]=='jump':cs.append((i,None,st,c.canonical(c.frame(sites[code[1]][0]))))
        else:cs.append((i,None,st,None))
    return ins,cs

def source(t):
    ss,_,_=base_source(t)
    inside=[(NEW_PREFIX+x[0][8:],x[1],x[2]) for x in ss if x[0][:8]==OLD_PREFIX]
    sites=sorted(outside+inside)
    ins,cs=make_contracts(sites)
    return sites,ins,cs
c.machine=lambda:(combined,labels)
c.source=source

def startup(rows,sites,bound=200000):
    targetpath=sites[25][0];head=-2
    physical=[0,0,0,0,0,0,2,0,0]+[1]*26
    target={head-1,head+48}|{head+i for i,b in enumerate(targetpath) if b}
    pos=head+49
    for v in physical:pos+=1;target.update(range(pos,pos+v+1));pos+=v+1
    tape=set();q=74;h=0
    for k in range(1,bound+1):
        if (q,int(h in tape))not in rows:return {'ok':False,'halt_at':k-1}
        w,d,q=rows[q,int(h in tape)]
        (tape.add if w else tape.discard)(h);h+=1 if d else -1
        if q==84 and h==head and tape==target:return {'ok':True,'steps':k}
    return {'ok':False,'bound':bound}

def export(out,t,rr,ch,ss,receipt):
    out.mkdir(parents=True,exist_ok=True)
    (out/'grammar.json').write_text(json.dumps(s.encode(t),indent=2)+'\n')
    (out/'folds.json').write_text(json.dumps(ch,indent=2)+'\n')
    (out/'sites.json').write_text(json.dumps(ss)+'\n')
    (out/'machine.native.tm').write_text(''.join(f'{q} {b} {w} {"R" if d else "L"} {n}\n' for(q,b),(w,d,n)in sorted(rr.items())))
    labs=[74]+sorted({q for q,b in rr}-{74})+[254];inv={q:i for i,q in enumerate(labs)}
    (out/'machine.tm').write_text(''.join(f'{inv[q]} {b} {w} {"R" if d else "L"} {inv[n]}\n'for q in labs[:-1] for b in(0,1) for w,d,n in[rr[q,b]]))
    (out/'labels.json').write_text(json.dumps(labs)+'\n')
    receipt['sha256']=hashlib.sha256((out/'machine.tm').read_bytes()).hexdigest()
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--ties',action='store_true');args=ap.parse_args()
    files=[AX/'diagonal196/grammar.json',AX/'separate196/grammar.json']
    if args.ties:files+=sorted((AX/'search/ties').glob('*.json'))
    out=ROOT/'research/cross_graft';out.mkdir(parents=True,exist_ok=True)
    receipts=[]
    for i,f in enumerate(files):
        t=c.read_grammar(f);rows,idx,sh=c.build(t);ch=s.bestcompatible_all(rows,sh);rr,ali=s.apply(rows,ch)
        rec={'grammar':str(f.relative_to(ROOT)),'fixed_states':len(rows)//2-len(sh),'AX_readers':len(sh),'folds':len(ch),'states':len(rr)//2}
        if i<2 or len(rr)//2<196:
            ss,ins,cs=c.source(t);rec['source_sites']=len(ss);rec['contracts']=c.validate(rr,cs);rec['startup']=startup(rr,ss)
            export(out/f'candidate_{i}',t,rr,ch,ss,rec)
        receipts.append(rec);print(json.dumps(rec),flush=True)
    (out/'summary.json').write_text(json.dumps(receipts,indent=2)+'\n')
if __name__=='__main__':main()
