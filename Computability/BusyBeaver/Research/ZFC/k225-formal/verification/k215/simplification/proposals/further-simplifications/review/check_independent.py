#!/usr/bin/env python3
"""Independent review: only literal source data are read; no fetched code is executed.
Finite corroboration and source consistency, not kernel proof.
"""
from pathlib import Path
from itertools import product
from collections import deque
import ast, hashlib, json, re, sys
if not __debug__ or sys.flags.optimize:
    raise SystemExit('Assertions must be enabled')
BASE=Path(__file__).resolve().parents[1]

def blob(data):
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()

def terminal():
    d=BASE/'terminal_contract'
    src=(d/'input/PositiveStutter.lean').read_bytes()
    pin=json.loads((d/'SOURCE_PIN.json').read_text())
    assert hashlib.sha256(src).hexdigest()==pin['sha256']
    assert blob(src)==pin['git_blob_sha']
    expected=src.decode().replace('namespace PositiveStutter','namespace TerminalDrain').replace('end PositiveStutter','end TerminalDrain').replace('plus terminal agreement at','plus terminal halting preservation at').replace('terminal : ∀ {a b}, R a b → (stepA a = none ↔ stepB b = none)','terminal : ∀ {a b}, R a b → stepA a = none → Halts stepB b').replace('exact halt_now ((hS.terminal hab).mp hd)','exact hS.terminal hab hd')
    actual=(d/'TerminalDrain.uncompiled.lean').read_text()
    assert actual[actual.index('import Init'):]==expected
    # Different implementation from the proposal: bounded orbit arrays suffice on finite systems.
    def orbit(t,s):
        result=[s]
        for _ in t:
            if result[-1] is None: break
            result.append(t[result[-1]])
        return result
    total=advanced=both=loose=0
    for a in product([None,0,1],repeat=2):
      ao=[orbit(a,i) for i in range(2)]; ah=[None in o for o in ao]
      for b in product([None,0,1,2],repeat=3):
        bo=[orbit(b,i) for i in range(3)]; bh=[None in o for o in bo]
        for bits in product([False,True],repeat=6):
          r=[(i,j) for i in range(2) for j in range(3) if bits[3*i+j]]
          advance=all(a[i] is None or any(v is not None and bits[3*a[i]+v] for v in bo[j][1:]) for i,j in r)
          drain=all(a[i] is not None or bh[j] for i,j in r)
          total+=1
          if advance:
            advanced+=1
            assert all(not bh[j] or ah[i] for i,j in r)
            if drain:
              both+=1
              assert all(ah[i]==bh[j] for i,j in r)
              loose+=any((a[i] is None)!=(b[j] is None) for i,j in r)
    prior=json.loads((d/'result.json').read_text())
    assert (total,advanced,both,loose)==tuple(prior[k] for k in ['systems_and_relations','advance_holds','advance_and_terminal_drain_hold','valid_relaxed_not_strict_terminal_agreement'])
    return {'source_and_derivative_exact':True,'systems_and_relations':total,'advance':advanced,'advance_and_drain':both,'strictness_witnesses':loose}

def table():
    text=(BASE/'runtime_contexts/inputs/KTable215.lean').read_text()
    raw=text.split('def table215 :',1)[1].split(':=',1)[1].split('\ndef tm215',1)[0]
    return ast.literal_eval(raw.replace('true','True').replace('false','False').replace('none','None').replace('some ',''))

def home():
    T=table(); qs=[2,3,5,9,15,23,34,50]
    for i,q in enumerate(qs):
        assert T[q][0]==(False,False,qs[i+1] if i<7 else 75)
        assert T[q][1]==(True,False,2)
    assert T[75]==((False,True,75),(True,True,84))
    # Absolute coordinates: initial R[0] is0 and current head is-1.
    # This deliberately does not use the worker's symbolic execution or macro implementation.
    def execute(w,r):
        original={-i-1:bool(b) for i,b in enumerate(w)}
        original.update({i:bool(b) for i,b in enumerate(r)})
        cells=original.copy();q,h,k=2,-1,0;visited=[]
        while q!=84 and k<4*len(w)+64:
            visited.append(h);b=cells.get(h,False);write,right,q=T[q][b]
            cells[h]=write;h+=1 if right else -1;k+=1
        assert q==84
        assert all(cells.get(i,False)==original.get(i,False) for i in set(cells)|set(original))
        return h,k,visited
    count=0
    for length in range(1,13):
      for u in product([False,True],repeat=length-1):
        w=u+(True,)
        if '00000000' in ''.join(str(int(x)) for x in w):continue
        for r in [(),(True,),(False,True,False,True),(True,True,False,False,True)]:
          h,k,visited=execute(w,r)
          assert (h,k)==(-length+1,length+18)
          assert max(visited)<=-1 # arbitrary R has not been inspected
          assert min(visited)==-length-9
          # Read the full target finite support, not only head/state.
          original={-i-1:bool(b) for i,b in enumerate(w)}
          original.update({i:bool(b) for i,b in enumerate(r)})
          left=[original.get(h-i-1,False) for i in range(length+10)]
          right=[original.get(h+i,False) for i in range(length-1+len(r))]
          assert left[0] is True and not any(left[1:])
          assert right==list(reversed(u))+list(r)
          count+=1
    bad=(False,)*8+(True,True)
    h,k,_=execute(bad,())
    assert h!=-len(bad)+1 and k!=len(bad)+18
    # General parameter guard: test selected affine words with disappearing one runs.
    def expand(segs,n):
        return tuple(b for b,a,c in segs for _ in range(a*n+c))
    symbolic=0
    for z1,z2,c,a in product(range(8),range(8),range(3),range(4)):
        segs=[(False,0,z1),(True,a,c),(False,0,z2),(True,0,1)]
        w0=expand(segs,0)
        if '00000000' in ''.join(str(int(x)) for x in w0):continue
        for n in [0,1,2,7,31]:
            w=expand(segs,n)
            assert '00000000' not in ''.join(str(int(x)) for x in w)
            assert execute(w,(True,False,True))[:2]==(-len(w)+1,len(w)+18)
            symbolic+=1
    return {'row_conditions':18,'independent_full_tape_runs':count,'selected_affine_word_runs':symbolic,'unsafe_eight_zero_word_rejected':True,'exact_physical_clock':'len(W)+18','arbitrary_right_suffix_unread':True}

def wf():
    d=BASE/'wellformedness/sources';nodes={};layer_counts={}
    for name in ['Dag222.lean','Dag219.lean','DagDom.lean','DagPerm.lean']:
        rows={}
        for m in re.finditer(r'^\s*\| (\d+) => (.+)$',(d/name).read_text(),re.M):
            es=re.findall(r'\.(node|inc|decnz|brk|cont|halt)(?:\s+(\d+))?',m[2])
            assert len(es)==2
            rows[int(m[1])]=tuple((op,int(a or 0)) for op,a in es)
        nodes.update(rows);layer_counts[name]=len(rows)
    assert set(nodes)==set(range(487))
    parents=[set() for _ in nodes];needed=[]
    for i in range(len(nodes)):
        children={a for op,a in nodes[i] if op=='node'}
        needed.append(len(children))
        for j in children:
            assert j in nodes
            parents[j].add(i)
    ready=deque(i for i,n in enumerate(needed) if n==0);summaries={};rank={}
    def edge(e):
        op,a=e
        if op=='node':return summaries[a]
        assert op not in ['brk','cont'] or a>0
        return (0,1 if op=='decnz' else a if op=='brk' else 0,a if op=='cont' else 0)
    while ready:
        i=ready.popleft();l,r=map(edge,nodes[i])
        summaries[i]=(max(l[0],r[0])+1,max(l[1]-1,r[1],0),max(l[2],r[2]-1,0))
        rank[i]=len(rank)+1
        for p in parents[i]:
            needed[p]-=1
            if needed[p]==0:ready.append(p)
    assert len(summaries)==487
    text=(d/'KSource215WfData.lean').read_text()
    for k,name in enumerate(['H','B','C']):
        given=list(map(int,re.search(r'def t'+name+r' : List Nat := \[([^]]*)\]',text,re.S)[1].replace('\n',' ').split(',')))
        assert given==[summaries[i][k] for i in range(487)]
    assert summaries[0]==(178,0,0)
    assert max(s[0] for s in summaries.values())<=487
    return {'bounded_nodes':487,'all_three_arrays_equal':True,'root_summary':summaries[0],'independent_algorithm':'Kahn readiness queue with unique child dependencies','all_nodes_processed':True,'row_layers':layer_counts}

def main():
    report={'status':'PASS_INDEPENDENT_FINITE_REVIEW_NOT_KERNEL_CHECKED','terminal_contract':terminal(),'home_contract':home(),'wellformedness':wf()}
    (BASE/'review/independent_result.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
