"""Frozen new direct-negation/diagonal composition; no optimizer required."""
from pathlib import Path
import sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'vendor'))
import compiler as c

INC=('leaf','inc',1)
INC7=('leaf','inc',7)
BREAK=('leaf','breakTo',1)
NTREE=(INC7,(INC7,'node64'))
_old_raw=c.raw_nodes
def raw_nodes():
    result=_old_raw();result['N']=NTREE;return result
c.raw_nodes=raw_nodes
c.MACROS['node64']=106
c.MACROS[INC7]=82
pair=(INC,INC)
c.MACROS[pair]=99
c.MACROS[(pair,pair)]=190

def build(t):
    old,_=c.machine()
    rows={(q,b):a for(q,b),a in old.items()if q<1300}
    index={};shape={}
    def state(t):
        if t=='N':return state(NTREE)
        if t in c.MACROS:return c.MACROS[t]
        if t in index:return index[t]
        if not c.isnode(t):raise ValueError(t)
        q=2000+len(index);index[t]=q;shape[q]=t
        for b,ch in enumerate(t):
            rows[q,b]=(0,False,302)if ch==BREAK else(b,True,state(ch))
        return q
    root=state(t);rows[101,1]=(1,True,root)
    return rows,index,shape

def fold(rows,chosen):
    alias={a:b for a,b,acts in chosen}
    actions={b:acts for a,b,acts in chosen}
    out={}
    for(q,bit),act in rows.items():
        if q in alias:continue
        w,d,n=actions[q][bit]if q in actions else act
        out[q,bit]=(w,d,alias.get(n,n))
    return out,alias

def check_local_folds(rows,folded,alias,chosen):
    for a,b,acts in chosen:
        for q,marker in((a,0),(b,1)):
            for v in(0,1):
                w,d,n=rows[q,v];target=alias.get(n,n)
                wanthead=1 if d else -1;expect={-1:marker,0:w}
                tape={-1:marker,0:v};pos=0;now=b
                for step in range(20):
                    if step and pos==wanthead and now==target and tape==expect:break
                    if pos not in tape:raise ValueError('unproved fold context')
                    act=folded.get((now,tape[pos]))
                    if act is None:raise ValueError('undefined fold action')
                    w2,d2,now=act;tape[pos]=w2;pos+=1 if d2 else -1
                else:raise ValueError('local fold did not rejoin')

def word(t):
    if t=='node60':return[INC,INC]
    if t=='node61':return[INC]*4
    if c.isnode(t):return word(t[0])+word(t[1])
    return[t]
