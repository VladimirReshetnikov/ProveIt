#!/usr/bin/env python3
"""Generate an untrusted offset-aware p227↔p230 test checkpoint certificate.

The paired straight-line segments are evaluated directly from the two full
source prefix trees. A kernel-checked generic checker is the intended final
consumer; the accompanying Python checks are a separate finite audit.
"""
from pathlib import Path
from functools import cache
from collections import Counter
import argparse,json,hashlib
import source_math as g
from build227 import normalize
HERE=Path(__file__).resolve().parent
class Program:
    def __init__(self,sites):
        self.root=g.tree(sites);self.maximum=max(len(p) for p,o,r in sites)
    @cache
    def tsite(self,P):
        t=self.root;i=0;Q=''
        while not g.is_leaf(t):
            b=P[i] if i<len(P) else '0';Q+=b;t=t[int(b)];i+=1
        return t,Q
    @staticmethod
    def inc(P):
        if not P:return ''
        return format((int(P,2)+1)%(1<<len(P)),f'0{len(P)}b')
    @staticmethod
    def cut(P,bit,k):
        if not k:return P
        ids=[i for i,b in enumerate(P) if b==bit]
        return P[:ids[-k]] if len(ids)>=k else ''
    @cache
    def seg(self,P):
        counts=[0]*9;steps=0;trace=[]
        for tick in range(1000):
            (op,r),Q=self.tsite(P)
            if op in('CD','CH'):return tuple(counts),P,steps,tuple(trace)
            trace.append((P,op,r))
            if op=='CI':counts[r]+=1;P=self.inc(Q)
            elif op=='CB':P=self.inc(self.cut(Q,'0',r))
            elif op=='CC':P=self.cut(Q,'1',r)
            else:raise ValueError(op)
            steps+=1
        raise ValueError('Segment fuel exhausted')
    def branch(self,P,positive):
        (op,r),Q=self.tsite(P);assert op=='CD'
        return self.inc(Q) if positive else self.inc(self.cut(Q,'0',1))
def bv(p):return '['+';'.join('true' if b=='1' else 'false' for b in p)+']'
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--candidate',type=Path,default=HERE/'generated/05_k227/sites.json');ap.add_argument('--out',type=Path,default=HERE/'offset_certificate');ap.add_argument('--name',default='227');a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True)
    refpath=HERE/'inputs/sites230.json'
    c=Program(json.loads(a.candidate.read_text()));r=Program(normalize(json.loads(refpath.read_text())))
    ccounts,cp,cs,ct=c.seg('');rcounts,rp,rs,rt=r.seg('')
    diff=[x-y for x,y in zip(ccounts,rcounts)];assert all(v==0 for i,v in enumerate(diff) if i!=5)
    entries=[(cp,rp,diff[5])];index={entries[0]:0};result=[];allbranches=[]
    def add(key):
        if key not in index:index[key]=len(entries);entries.append(key)
        return index[key]
    for number,(P,Q,delta) in enumerate(entries):
        (cop,cr),CP=c.tsite(P);(rop,rr),RQ=r.tsite(Q)
        assert(cop,cr)==(rop,rr),(number,P,Q,(cop,cr),(rop,rr))
        assert delta in(0,1),(number,delta)
        row={'index':number,'candidate_pc':P,'reference_pc':Q,'offset_R5':delta,'opcode':cop,'register':cr}
        if cop=='CH':
            assert delta==0;row.update(positive_index=0,zero_index=0)
        else:
            assert cop=='CD' and (cr!=5 or delta==0),(number,cr,delta)
            for positive in(True,False):
                inc1,p1,n1,tr1=c.seg(c.branch(P,positive));inc2,p2,n2,tr2=r.seg(r.branch(Q,positive))
                ds=[v-w for v,w in zip(inc1,inc2)];assert all(v==0 for i,v in enumerate(ds) if i!=5),(number,positive,ds)
                nextdelta=delta+ds[5];j=add((p1,p2,nextdelta));name='positive_index' if positive else 'zero_index';row[name]=j
                allbranches.append({'entry':number,'positive':positive,'successor':j,'candidate_increments':inc1,'reference_increments':inc2,'candidate_segment_steps':n1,'reference_segment_steps':n2,'offset_before':delta,'offset_after':nextdelta})
        result.append(row)
    assert len(entries)==len(result)
    (a.out/'certificate.json').write_text(json.dumps({'format':'rm-single-register-offset-bisimulation-v1','offset_convention':'candidate R5 = reference R5 + offset_R5; all other registers equal','entries':result},indent=2)+'\n')
    (a.out/'branches.json').write_text(json.dumps(allbranches,indent=2)+'\n')
    coq='''(** Generated untrusted paired checkpoint certificate; checked by the offset-aware Bisim checker. *)
From Coq Require Import List NArith ZArith.
Import ListNotations.
Definition CERTNAME : list (list bool * list bool * Z * N * N) := [
'''+ ';\n'.join(f'  ({bv(e["candidate_pc"])}, {bv(e["reference_pc"])}, {e["offset_R5"]}%Z, {e["positive_index"]}%N, {e["zero_index"]}%N)' for e in result)+'\n].\n'
    coq=coq.replace('CERTNAME',f'cert{a.name}_offsets')
    (a.out/f'Cert{a.name}Offsets.v').write_text(coq)
    counts=Counter(e['offset_R5'] for e in result)
    report={'status':'PAIRED_OFFSET_SEGMENT_CERTIFICATE_PASS','candidate_source_sha256':hashlib.sha256(a.candidate.read_bytes()).hexdigest(),'reference_source_sha256':hashlib.sha256(refpath.read_bytes()).hexdigest(),'entries':len(entries),'checked_branches':len(allbranches),'offset_entry_counts':dict(counts),'offset_register':5,'tested_register_at_nonzero_offset':sorted({e['register'] for e in result if e['offset_R5']}),'initial_candidate_steps':cs,'initial_reference_steps':rs,'initial_offset_R5':diff[5],'maximum_segment_steps':max(max(e['candidate_segment_steps'],e['reference_segment_steps']) for e in allbranches),'nonzero_offset_entries':[e for e in result if e['offset_R5']]}
    (a.out/'verification.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
