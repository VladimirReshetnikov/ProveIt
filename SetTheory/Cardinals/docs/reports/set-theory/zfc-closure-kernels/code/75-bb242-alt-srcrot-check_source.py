#!/usr/bin/env python3
"""Check all four additional transfer-plus-one rotations in combined243.

Standard-library-only source checker. The mathematical induction stated in
source_rotation.tex closes the finite symbolic and context certificates.
Neither this script nor a source-DAG count asserts a smaller binary machine.
"""
from pathlib import Path
import argparse,hashlib,json

PREFIXES = ['11101001001011000011', '1110100100101110011',
            '1110100101100011', '111110011']
OLD_SHA = '3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4'

def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def inc(s):
    out=list(s)
    for i in range(len(out)-1,-1,-1):
        if out[i]=='0':
            out[i]='1';break
        out[i]='0'
    return ''.join(out)

def jump(s,bit,n):
    assert n>0
    j=len(s)
    while n and j:
        j-=1
        n-=s[j]==bit
    return inc(s[:j]) if bit=='0' else s[:j]

class Source:
    def __init__(self,rows):
        self.rows=rows;self.leaves={};pref=set()
        for i,(p,o,r)in enumerate(rows):
            assert p and set(p)<={'0','1'} and p not in self.leaves
            assert ((o in ('CI','CD')and type(r)is int and 0<=r<9)
                    or(o in ('CB','CC')and type(r)is int and r>=1)
                    or(o=='CH'and r is None))
            self.leaves[p]=i;pref.update(p[:j]for j in range(len(p)))
        assert not pref.intersection(self.leaves)
        assert list(self.leaves)==sorted(self.leaves)
        both=pref|self.leaves.keys()
        assert all(p+'0'in both and p+'1'in both for p in pref)
        self.depth=max(map(len,self.leaves))
    def at(self,p):
        for n in range(1,self.depth+1):
            q=(p+'0'*n)[:n]
            if q in self.leaves:
                assert set(p[n:])<={'0'}
                return self.leaves[q]
        raise AssertionError(('incomplete tree',p))
    def edges(self,i):
        p,o,r=self.rows[i]
        if o=='CI':d={'inc':inc(p)}
        elif o=='CD':d={'zero':jump(p,'0',1),'positive':inc(p)}
        elif o=='CB':d={'control':jump(p,'0',r)}
        elif o=='CC':d={'control':jump(p,'1',r)}
        else:assert o=='CH';return {}
        return {k:self.at(v)for k,v in d.items()}

def block(s,start,n,zero):
    lower=[0]*9;upper=[None]*9;delta=[0]*9;trace=[];i=start
    if zero:upper[6]=0
    else:lower[6]=1
    for _ in range(n):
        _,op,r=s.rows[i]
        if op=='CI':
            lower[r]+=1;delta[r]+=1
            if upper[r]is not None:upper[r]+=1
            branch='inc'
        elif op=='CD':
            if upper[r]==0:branch='zero'
            else:
                assert lower[r]>=1
                lower[r]-=1;delta[r]-=1
                if upper[r]is not None:upper[r]-=1
                branch='positive'
        else:
            assert op in ('CB','CC');branch='control'
        j=s.edges(i)[branch];trace.append([i,branch,j]);i=j
    return dict(exit=i,delta=delta,lower=lower,upper=upper,trace=trace)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args();assert __debug__
    assert digest(a.baseline)==OLD_SHA
    oldrows=json.loads(a.baseline.read_text());old=Source(oldrows)
    assert len(oldrows)==6459
    newrows=oldrows.copy();groups=[]
    for p in PREFIXES:
        before=[[p+'00','CD',6],[p+'010','CI',5],[p+'011','CC',2],[p+'1','CI',5]]
        assert [r for r in oldrows if r[0].startswith(p)]==before
        after=[[p+'0','CI',5],[p+'10','CD',6],[p+'11','CC',2]]
        newrows=[r for r in newrows if not r[0].startswith(p)]+after
        groups.append((p,before,after))
    newrows.sort();new=Source(newrows);assert len(newrows)==6455
    removed={old.leaves[p]for _,before,_ in groups for p,_,_ in before}
    mapping={i:new.leaves[p]for i,(p,_,_)in enumerate(oldrows)if i not in removed}
    entries={}
    for p,before,after in groups:
        i,j=old.leaves[before[0][0]],new.leaves[after[0][0]]
        mapping[i]=j;entries[i]=[]
    edges=0
    for i,j in mapping.items():
        if i in entries:continue
        assert oldrows[i][1:]==newrows[j][1:]
        oe,ne=old.edges(i),new.edges(j);assert oe.keys()==ne.keys()
        for branch,k in oe.items():
            assert k in mapping,('external entry into fragment interior',i,k)
            assert mapping[k]==ne[branch],(i,j,branch,k,ne[branch])
            if k in entries:entries[k].append([i,branch])
            edges+=1
    blocks=[]
    for p,before,after in groups:
        i,j=old.leaves[before[0][0]],new.leaves[after[0][0]]
        old_exit=old.edges(i+3)['inc'];new_exit=new.edges(j+1)['zero']
        assert old_exit in mapping and mapping[old_exit]==new_exit
        assert old.edges(i)=={'zero':i+3,'positive':i+1}
        assert old.edges(i+1)=={'inc':i+2}and old.edges(i+2)=={'control':i}
        assert new.edges(j)=={'inc':j+1}
        assert new.edges(j+1)=={'zero':new_exit,'positive':j+2}
        assert new.edges(j+2)=={'control':j}
        for zero,n in [(True,2),(False,3)]:
            x,y=block(old,i,n,zero),block(new,j,n,zero)
            delta=[0]*9;delta[5]=1
            if not zero:delta[6]=-1
            assert x['delta']==y['delta']==delta
            assert x['lower']==y['lower']and x['upper']==y['upper']
            assert (x['exit'],y['exit'])==((old_exit,new_exit)if zero else(i,j))
            blocks.append(dict(prefix=p,guard='R6=0'if zero else'R6>=1',steps=n,old=x,new=y))
    assert mapping[old.at('')]==new.at('')
    halt_old=[i for i,r in enumerate(oldrows)if r[1]=='CH']
    halt_new=[i for i,r in enumerate(newrows)if r[1]=='CH']
    assert len(halt_old)==len(halt_new)==1 and mapping[halt_old[0]]==halt_new[0]
    a.output.mkdir(parents=True,exist_ok=True)
    dest=a.output/'sites_logical.json';dest.write_text(json.dumps(newrows,indent=2)+'\n')
    result=dict(status='PASS_UNIVERSAL_SOURCE_ROTATIONS',baseline_sha256=OLD_SHA,
        source_sha256=digest(dest),source_leaves_before=len(oldrows),source_leaves_after=len(newrows),
        cases_before=sum(2 if r[1]=='CD'else 1 for r in oldrows),
        cases_after=sum(2 if r[1]=='CD'else 1 for r in newrows),
        context_edges_checked=edges,external_entries=entries,
        halt_site_before=halt_old[0],halt_site_after=halt_new[0],
        universal_blocks=blocks,assumptions='All nine natural-valued registers arbitrary at fragment entry.',
        local_normal_form='R5_out=R5_in+R6_in+1; R6_out=0; other registers unchanged.',
        local_steps='3*R6_in+2 in both fragments.',
        limitation='Finite symbolic/context certificate plus ordinary induction. No kernel proof or state-count saving inferred.')
    (a.output/'source-verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k!='universal_blocks'},indent=2))

if __name__=='__main__':main()
