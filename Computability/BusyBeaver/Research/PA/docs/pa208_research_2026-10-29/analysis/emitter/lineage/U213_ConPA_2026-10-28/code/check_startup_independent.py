#!/usr/bin/env python3
"""Independent finite startup and source-prefix check; no project imports."""
from pathlib import Path
import json,hashlib,argparse

def need(ok,msg):
    if not ok:raise ValueError(msg)

def table(path):
    out={};start=[]
    for l in path.read_text().splitlines():
        if l.startswith('#! start '):start.append(int(l[9:]));continue
        if not l or l.startswith('#'):continue
        q,b,w,d,z=l.split();q,b,w,z=map(int,(q,b,w,z))
        need((q,b)not in out and b in (0,1) and w in (0,1) and d in ('L','R'),'row')
        out[q,b]=(w,1 if d=='R'else -1,z)
    need(start==[0],'start');return out

def source_graph(rows):
    indices={p:i for i,(p,_,_)in enumerate(rows)}
    need(len(indices)==len(rows),'duplicate source address')
    ints={}
    def visit(p):
        if p in indices:ans=(indices[p],indices[p]+1)
        else:
            a,b=visit(p+'0'),visit(p+'1');need(a[1]==b[0],'tree order');ans=a[0],b[1]
        ints[p]=ans;return ans
    need(visit('')==(0,len(rows)),'source coverage')
    def jump(p,bit,n):
        for j in range(len(p)-1,-1,-1):
            if p[j]==bit:
                n-=1
                if n==0:return ints[p[:j]][1 if bit=='0'else 0]%len(rows)
        return 0
    graph=[]
    for i,(p,op,arg)in enumerate(rows):
        nxt=(i+1)%len(rows)
        if op=='CD':graph.append([jump(p,'0',1),nxt])
        elif op=='CB':graph.append([jump(p,'0',arg)])
        elif op=='CC':graph.append([jump(p,'1',arg)])
        elif op=='CI':graph.append([nxt])
        else:need(op=='CH','opcode');graph.append([])
    return graph

def audit(tm,source):
    T=table(tm);rows=json.load(open(source));g=source_graph(rows)
    states={q for q,b in T}
    need(len(states)==213 and len(T)==426,'count')
    need(set(T)=={(q,b)for q in states for b in (0,1)},'total table')
    need({z for w,d,z in T.values()}-states=={254},'halt')
    q=h=0;ones=set();sha=hashlib.sha256()
    for t in range(48140):
        b=int(h in ones);w,d,z=T[q,b]
        sha.update((json.dumps([t,q,h,b,w,d,z],separators=(',',':'))+'\n').encode())
        if w:ones.add(h)
        else:ones.discard(h)
        q,h=z,h+d
    need((q,h)==(84,-2),'binary endpoint')
    pc='001100110101010';regs=[1,0,13,0,0,1,0,0,1]
    need(rows[136][0]==pc,'source address')
    permutation=(6,2,0,4,3,7,8,5,1);phys=[0]*9
    for i,j in enumerate(permutation):phys[j]=regs[i]
    want={-3,54}|{h+i for i,c in enumerate(pc)if c=='1'}
    pos=55
    for n in phys+[1]*43:
        want.update(range(pos+1,pos+n+2));pos+=n+2
    need(ones==want,'complete tape including zero exterior')
    need(len(ones)==120,'one count')
    ip=106;R=[1,0,4,0,0,1,0,0,1];source_trace=[]
    for t in range(141):
        old=ip;before=R.copy();p,op,a=rows[ip]
        if op=='CI':R[a]+=1;ip=g[ip][0]
        elif op=='CD':positive=R[a]>0;R[a]-=int(positive);ip=g[ip][int(positive)]
        elif op in ('CB','CC'):ip=g[ip][0]
        else:raise ValueError('early source halt')
        source_trace.append([old,before,ip,R.copy()])
    need((ip,R)==(136,regs),'source prefix endpoint')
    return {'status':'INDEPENDENT_213_STARTUP_AND_SUFFIX_PREFIX_PASS',
        'working_states':213,'rows':426,'literal_steps':48140,
        'state':q,'head':h,'header':54,'header_distance':56,'additional_gap':0,
        'source_ordinal':136,'source_address':pc,'registers':regs,
        'spares':[1]*43,'one_cells':sorted(ones),
        'source_seed_ordinal':106,'source_seed':[1,0,4,0,0,1,0,0,1],
        'source_steps':141,'source_trace':source_trace,
        'literal_delta_sha256':sha.hexdigest(),
        'table_sha256':hashlib.sha256(tm.read_bytes()).hexdigest(),
        'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
        'scope':'Finite exact tape and source-prefix check. Suffix safety, credit, source calibration, and arbitrary-register binary simulation remain separate obligations.'}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('table',type=Path);p.add_argument('source',type=Path);p.add_argument('output',type=Path);a=p.parse_args()
    out=audit(a.table,a.source);a.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items()if k not in ('source_trace','one_cells','spares')},indent=2))
