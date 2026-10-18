#!/usr/bin/env python3
"""Emit protocol variants through the attributed optimized native decoder.

State reuse follows source27's structural fingerprint hints. Every accepted
table must pass every new literal source-program guard with unchanged unary
register boxes. A runtime table is not a blank-start consistency machine.
"""
from __future__ import annotations
from collections import Counter
from functools import lru_cache
from itertools import product
from pathlib import Path
import hashlib,json,sys,time
HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'source/Computability/BusyBeaver/Research/ZFC'
sys.path.insert(0,str(BASE))
import candidate252_independent_audit as audit
import breakthrough_register_permutation as a
import mp_protocol_runtime as runtime
from permutation252_fold_search import Tracking

DATA=HERE.parent/'source/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/27-variant-experiments-machine_search-grammar_search-decoder_entries.json'
OLD=json.loads(DATA.read_text())
NODES={int(n):tuple(map(tuple,e)) for n,e in OLD['nodes'].items()}
ROOT=OLD['root']
OLD_FP={f:int(n) for n,f in OLD['fingerprints'].items()}


def patch_path(edits):
    """Context-specific substitution, then exact structural interning."""
    out,intern={},{}
    def pair(left,right):
        item=left,right
        if item not in intern:
            q=len(out);out[q]=item;intern[item]=q
        return ('N',intern[item])
    @lru_cache(None)
    def copy(edge):
        if edge[0] in ('N','T'):
            left,right=NODES[edge[1]] if edge[0]=='N' else edge[1:]
            return pair(copy(left),copy(right))
        return edge
    def visit(edge,path):
        if path in edits:return copy(edits[path])
        if not any(p.startswith(path) for p in edits):return copy(edge)
        assert edge[0]=='N'
        left,right=NODES[edge[1]]
        return pair(visit(left,path+'0'),visit(right,path+'1'))
    root=visit(('N',ROOT),'')[1]
    return out,root


def emit(nodes,root,base):
    @lru_cache(None)
    def fp(edge):
        if edge[0]=='N':
            text='N('+','.join(fp(e) for e in nodes[edge[1]])+')'
        else:text=':'.join(map(str,edge))
        return hashlib.sha256(text.encode()).hexdigest()
    modal=lambda counts:max(counts,key=counts.get)
    control={}
    for n,es in NODES.items():
        for bit,e in enumerate(es):
            if e[0] not in ('B','C'):continue
            counts=control.setdefault((e,bit),Counter())
            for q,weight in OLD['state_entries'][str(n)].items():counts[base[q,bit]]+=weight
    table=base.copy();entry={};allocate=255
    for n in nodes:
        f=fp(('N',n))
        if n==root:entry[n]='96'
        elif f in OLD_FP:entry[n]=modal(OLD['state_entries'][str(OLD_FP[f])])
        else:entry[n]=str(allocate);allocate+=1
    def transition(e,bit,n):
        if e[0]=='N':return bit,'R',entry[e[1]]
        # The newly exposed NIP break follows a zero path bit. In this context
        # old48, rather than source27's default old33, erases that zero before
        # carrying into the enclosing prefix. Every complete guard is checked.
        if e==('B',1):
            if bit==0:return 0,'L','7'
            return 0,'L','48' if nodes[n]==(('D',5),('B',1)) else '33'
        if e[0] in ('B','C'):return control[e,bit].most_common(1)[0][0]
        return bit,'R',modal(OLD['leaf_entries'][':'.join(map(str,e))])
    for n,es in nodes.items():
        if n==root or fp(('N',n)) not in OLD_FP:
            for bit,e in enumerate(es):table[entry[n],bit]=transition(e,bit,n)
    return table,entry


def native_sites(nodes,root):
    result=[]
    def visit(edge,path):
        if edge[0]=='N':
            for bit,e in enumerate(nodes[edge[1]]):visit(e,path+str(bit))
        else:
            k=edge[0];r=edge[1] if len(edge)>1 else None
            result.append((path,'C'+k,a.PHYS[r] if k in ('I','D') else r))
    visit(('N',root),'');return result


def closed_run(expr,registers,fuel=10000):
    """Independent exact register interpreter for a proposed closed routine."""
    p='';regs=registers[:]
    def walk(edge,path):
        used=''
        while edge[0] in ('N','T'):
            bit=path[len(used)] if len(used)<len(path) else '0';used+=bit
            es=NODES[edge[1]] if edge[0]=='N' else edge[1:]
            edge=es[int(bit)]
        return edge,used
    def carry(path):
        i=path.rfind('0')
        return None if i<0 else path[:i]+'1'+'0'*(len(path)-i-1)
    for step in range(fuel):
        e,p=walk(expr,p);op=e[0];r=e[1] if len(e)>1 else None
        if op=='H':return 'halt',regs,step+1
        if op=='I':regs[r]+=1;p=carry(p)
        elif op=='D':
            if regs[r]:regs[r]-=1;p=carry(p)
            else:p=carry(a.strip(p,'0',1))
        elif op=='B':p=carry(a.strip(p,'0',r))
        elif op=='C':p=a.strip(p,'1',r)
        if p is None:return 'normal',regs,step+1
    return 'fuel',regs,fuel


def main():
    base,_=runtime.generate()
    # generate() applies MP; restore the original table for combinatorial lanes.
    base['204',1]=(1,'R','113')
    transfer_h_t=('T',('D',5),('T',('I',1),('C',2)))
    drop=('T',('N',39),transfer_h_t)
    niptest=('T',('D',5),('T',('T',('D',5),('B',1)),('H',)))
    nip=('T',niptest,('T',('N',166),('N',187)))
    # All nine registers accounted for; scratch zero is a command-boundary
    # hypothesis. Literal independent tests verify both nonhalting effects.
    checks=[]
    for h in range(8):
        regs=[11,0,0,13,17,h,0,0,19]
        status,out,steps=closed_run(nip,regs)
        want=regs[:];want[5]=0
        assert (status=='halt')==(h==1)
        if h!=1:assert out==want,(h,out,want)
        checks.append(dict(routine='nip',h=h,status=status,steps=steps))
        regs=[11,2,0,13,17,h,0,0,19]
        status,out,steps=closed_run(drop,regs)
        # Cantor P(2,0)=3. Source push with empty stack stores exactly that.
        want=regs[:];want[1]=h;want[2]=3;want[5]=0
        assert status=='normal' and out==want,(h,out,want)
        checks.append(dict(routine='drop',h=h,status=status,steps=steps))
    outdir=HERE/'native_variants';outdir.mkdir(exist_ok=True)
    records=[];began=time.monotonic()
    for ax,mp,dr,np in product((False,True),repeat=4):
        flags=dict(ax_shift=ax,mp_zero_removed=mp,drop_consumes_cache=dr,nip_specialized=np)
        edits={}
        if ax:edits['111010010010000']=('N',42)
        if mp:edits['111111']=('N',42)
        if dr:edits['1110101']=drop
        if np:edits['1110100101']=nip
        nodes,root=patch_path(edits)
        record=dict(flags=flags,decoder_nodes=len(nodes))
        try:table,entry=emit(nodes,root,base)
        except KeyError as e:
            record['outcome']='unsupported_exposed_leaf';record['error']=str(e);records.append(record);continue
        assert all(table[str(q),b]==base[str(q),b] for q,b in audit.BOX_PAIRS)
        a.sites=native_sites(nodes,root);guards=runtime.guards();tracked=Tracking(table)
        record['guards']=len(guards)
        record['affine']=runtime.certify(tracked,guards)
        if record['affine']['passed']:
            used=tracked.used|{(str(q),b) for q,b in audit.BOX_PAIRS}
            states={q for q,b in used}|{'64','96'}
            pruned={}
            for (q,b),(w,d,t) in table.items():
                if q not in states:continue
                if t not in states|{'254'}:
                    assert (q,b) not in used;t='64'
                pruned[q,b]=w,d,t
            assert len(pruned)==2*len(states)
            record.update(outcome='conditional_runtime_pass',working_states=len(states),
                          allocated_before_pruning=len(table)//2,used_pairs=len(used))
            tag=''.join(str(int(x)) for x in (ax,mp,dr,np))
            (outdir/(tag+'.tm')).write_bytes(a.encoded(pruned))
            (outdir/(tag+'.json')).write_text(json.dumps(dict(root=root,nodes=nodes),indent=2)+'\n')
            record['table']=tag+'.tm';record['table_sha256']=hashlib.sha256(a.encoded(pruned)).hexdigest()
        else:record['outcome']='affine_failure'
        records.append(record)
        print(flags,record.get('working_states'),record['outcome'],record['affine'],flush=True)
    report=dict(scope=__doc__,attribution='Mira-Cult/Jeff/Wade; mira-emmy public253; ProveIt permutation252; source27 cost_search emitter algorithm.',
                source203_sha256=hashlib.sha256(DATA.read_bytes()).hexdigest(),
                independent_routine_checks=checks,records=records,seconds=time.monotonic()-began)
    (outdir/'results.json').write_text(json.dumps(report,indent=2)+'\n')


if __name__=='__main__':main()
