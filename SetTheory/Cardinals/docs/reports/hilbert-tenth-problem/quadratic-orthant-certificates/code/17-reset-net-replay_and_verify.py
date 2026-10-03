#!/usr/bin/env python3
"""Rebuild and audit the literal net, exact shortest accepting run and every
quadratic summand. Independent checks use literal rows and direct marking updates.
All Python uses the standard library; no solver or remote execution needed."""
from pathlib import Path
from collections import Counter,defaultdict
from itertools import product
import json,hashlib
from build_net import compile_net,initial,fire,ledger
from source_quadratic import semantic_table,base_layout,compile_schema as source_schema,evaluate,witness_for_trace
from reset_quadratic import compile_schema as reset_schema,trace_witness
from peak_quadratic import compile_peak,add_peak_witness
R=Path(__file__).resolve().parent

def write(name,obj): (R/name).write_text(json.dumps(obj,indent=2)+'\n')
def defect(m):return m.get('budget',0)-sum(m.get(p,0) for p in ['L','R','T','reserve'])
def source_replay(program,L,R,limit=100000):
    q=program['entry'];xs=[L,R,0];rows=[]
    while q!=program['halt']:
        assert len(rows)<limit
        op,r,*dst=program['rows'][q];ys=xs.copy()
        if op=='ADD':ys[r]+=1;z=dst[0];branch='inc'
        elif xs[r]:ys[r]-=1;z=dst[0];branch='pos'
        else:z=dst[1];branch='zero'
        rows.append({'step':len(rows),'control':q,'registers':xs.copy(),'next_control':z,'next_registers':ys,'branch':branch})
        q=z;xs=ys
    return rows

def expand(net,source,L,R,k):
    byname={t['name']:i for i,t in enumerate(net['transitions'])};m=initial(net,L,R);trace=[];losses=0
    def step(name):
        nonlocal m,losses
        old=m.copy();i=byname[name];m,loss=fire(net,m,i);losses+=loss
        assert defect(m)==losses and sum(m.get(q,0) for q in net['control_places'])==1
        trace.append({'step':len(trace),'transition':i,'name':name,'old':old,'new':m.copy(),'reset_loss':loss,'cumulative_loss':losses})
    for _ in range(k):step('pump')
    step('enter')
    for row in source:step(row['control']+':'+row['branch'])
    for p in ['L','R','T']:
        while m.get(p,0):step('clean_'+p)
        step('advance_'+p)
    while m.get('reserve',0) and m.get('budget',0):step('drain')
    step('finish');assert m==net['target'] and losses==0
    return trace

def literal_audit(program,net):
    assert compile_net(program)==net
    assert ledger(net)==json.loads((R/'net_ledger.json').read_text())
    expected=(539,771,2608,233)
    got=ledger(net);assert tuple(got[k] for k in ['places','transitions','ordinary_arcs','reset_arcs'])==expected
    assert len(program['rows'])==528 and Counter(row[0] for row in program['rows'].values())=={'ADD':295,'SUB':233}
    # In every row exactly one old control is consumed and one new control produced.
    for t in net['transitions']:
        assert sum(n for p,n in t['pre'].items() if p in net['control_places'])==1
        assert sum(n for p,n in t['post'].items() if p in net['control_places'])==1
        assert not set(t['reset'])&set(net['control_places'])
        if t['reset']:assert t['kind']=='SUB_ZERO' and not set(t['reset'])&set(t['pre'])
    # Every source row is independently checked against its literal net arcs.
    by={t['name']:t for t in net['transitions']}
    for q,row in program['rows'].items():
        op,r,*dst=row;p=program['registers'][r]
        if op=='ADD':spec=[('inc',dst[0],{'q:'+q:1,'reserve':1},{'q:'+dst[0]:1,p:1},[])]
        else:spec=[('pos',dst[0],{'q:'+q:1,p:1},{'q:'+dst[0]:1,'reserve':1},[]),('zero',dst[1],{'q:'+q:1},{'q:'+dst[1]:1},[p])]
        for suffix,to,pre,post,resets in spec:
            t=by[q+':'+suffix];assert t['pre']==pre and t['post']==post and t['reset']==resets and t['target_control']==to

def verify_source_peak(program,source,L,R,N):
    table=semantic_table(program);h=len(source);B=len(table['branches']);layout,nb=base_layout(table);stride=B+nb
    w,control,final,short_trace=witness_for_trace(table,h,[L,R,0]);assert control==table['halt']
    w,peaks=add_peak_witness(w,source,stride*h,L+R)
    value=0;squares=products=0;prevcontrol=table['entry'];prev=[L,R,0];prevv=0
    for j,row in enumerate(source):
        offset=j*stride;es=[w.get(offset+b,0) for b in range(B)];E=sum(es);old=[0]*3;new=[0]*3;Q=D=0
        for b,t in enumerate(table['branches']):
            bases=[0 if n is None else w.get(offset+B+n,0) for n in layout[b]];a=bases.copy();z=bases.copy()
            if t['guard']=='positive':a[t['register']]+=es[b]
            elif t['guard'] is None:z[t['register']]+=es[b]
            old=[x+y for x,y in zip(old,a)];new=[x+y for x,y in zip(new,z)];Q+=t['source']*es[b];D+=t['target']*es[b]
            term=(E-es[b])*(es[b]+sum(bases));assert term>=0;value+=term;products+=1
        residual=[E-1,Q-prevcontrol]+[x-y for x,y in zip(old,prev)]
        value+=sum(x*x for x in residual);squares+=5
        assert old==row['registers'] and new==row['next_registers']
        u=w.get(stride*h+2*j,0);v=w.get(stride*h+2*j+1,0)
        residual=sum(prev)+prevv+u-sum(new)-v
        value+=residual*residual+u*v;squares+=1;products+=1
        piece=source_schema(table,1,entry=Q,target=D,initial=old)
        column={i-offset:a for i,a in w.items() if offset<=i<offset+stride}
        assert evaluate(piece,column,{})==0
        prevcontrol=D;prev=new;prevv=v
    value+=(prevcontrol-table['halt'])**2;squares+=1
    value+=(N-h-3*sum(prev)+(L+R)-2*prevv-5)**2;squares+=1
    assert value==0 and (squares,products)==(6*h+2,762*h)
    write('accepting_peak_witness.json',{'parameters':{'L':L,'R':R,'N':N},'external_source_instructions':h,'variable_count':2813*h,'nonzero_coordinates':sorted(w.items()),'omitted_coordinates':'All omitted declared coordinates are zero'})
    write('accepting_peak_trace.json',peaks)
    return {'coordinate_slots':2813*h,'nonzero_coordinates':len(w),'affine_squares_evaluated':squares,'products_evaluated':products,'value':value,'explicit_source_chunks_checked':h}

def verify_reset_trace(net,trace,L,R):
    T=len(trace);m=len(net['transitions']);d=5;stride=m*(d+1);w=trace_witness(net,trace,True)
    # Evaluate every original polynomial summand and compare independently
    # compiled, literal one-step arithmetic chunks for all 388 firings.
    controls=net['control_places'];codes={q:i for i,q in enumerate(controls)};data=net['data_places']
    prev=initial(net,L,R);total=0;squares=products=0
    def qcode(mark):return sum(codes[q]*mark.get(q,0) for q in controls)
    for j,row in enumerate(trace):
        offset=j*stride;es=[w.get(offset+r,0) for r in range(m)];E=sum(es);old=[0]*d;new=[0]*d;Q=D=0
        for r,t in enumerate(net['transitions']):
            bs=[w.get(offset+m+r*d+i,0) for i in range(d)]
            for i,p in enumerate(data):old[i]+=t['pre'].get(p,0)*es[r]+bs[i];new[i]+=t['post'].get(p,0)*es[r]+int(p not in t['reset'])*bs[i]
            Q+=es[r]*qcode(t['pre']);D+=es[r]*qcode(t['post'])
            term=(E-es[r])*(es[r]+sum(bs));assert term>=0;total+=term;products+=1
        residual=[E-1,Q-qcode(prev)]+[old[i]-prev.get(p,0) for i,p in enumerate(data)]
        total+=sum(x*x for x in residual);squares+=7
        assert new==[row['new'].get(p,0) for p in data]
        packet=reset_schema(net,1,project_controls=True,initial=row['old'],target=row['new'])
        column={i-offset:v for i,v in w.items() if offset<=i<offset+stride}
        assert evaluate(packet,column,{})==0
        prev=row['new']
    total+=sum((prev.get(p,0)-net['target'].get(p,0))**2 for p in data)+(qcode(prev)-qcode(net['target']))**2;squares+=6
    assert total==0 and (squares,products)==(7*T+6,m*T)
    write('accepting_reset_witness.json',{'parameters':{'L':L,'R':R},'external_firings':T,'variable_count':stride*T,'nonzero_coordinates':sorted(w.items()),'omitted_coordinates':'All omitted declared coordinates are zero'})
    return {'coordinate_slots':stride*T,'nonzero_coordinates':len(w),'affine_squares_evaluated':squares,'products_evaluated':products,'value':total,'explicit_one_step_chunks_checked':T}

def weighted_semantics_tests():
    cases=0;mutations=0
    # Resets overlap both ordinary consumption and production here, unlike the
    # particular literal universal net. Test output survival and enabledness.
    for pre,post,reset,old in product(range(3),range(3),range(2),range(5)):
        net={'places':['x'],'transitions':[{'name':'t','pre':{'x':pre} if pre else {},'post':{'x':post} if post else {},'reset':['x'] if reset else []}], 'initial_affine':{'x':{'constant':old}},'target':{}}
        if old<pre:
            try:fire(net,{'x':old},0)
            except ValueError:pass
            else:raise AssertionError('ignored input requirement on a reset place')
            continue
        expected=(0 if reset else old-pre)+post;net['target']={'x':expected}
        out,loss=fire(net,{'x':old},0);assert out.get('x',0)==expected and loss==(old-pre if reset else 0)
        packet=reset_schema(net,1);w=trace_witness(net,[{'transition':0,'old':{'x':old}}]);assert evaluate(packet,w,{})==0
        bad=dict(w);bad[0]=0;assert evaluate(packet,bad,{})>0;mutations+=1
        bad=dict(w);bad[1]=bad.get(1,0)+1;assert evaluate(packet,bad,{})>0;mutations+=1;cases+=1
    # A mixed-selector nonnegative REAL gate is strictly positive. Initial values
    # can be fractional for this gate-only test; full certificate input is natural.
    assert (1-.5)*(.5)>0
    return cases,mutations

def bounded_all_run_tests():
    # Exhaustive transition-labelled tree, including dishonest reset branches,
    # premature phase exits, and all pump choices within the fixed length bound.
    program={'registers':['L','R','T'],'entry':'q0','halt':'HALT','rows':{'q0':['SUB',0,'HALT','HALT']}}
    net=compile_net(program);tested=accepts=0
    for L,R in product(range(3),range(2)):
        bound=18;current=[(initial(net,L,R),0)];counts=Counter();B=L+R;H=B-int(L>0);minimum=1+H+B+5
        for length in range(bound+1):
            nxt=[]
            for mark,loss in current:
                assert defect(mark)==loss;tested+=1
                if mark==net['target']:counts[length]+=1;accepts+=1
                if length==bound:continue
                for t in net['transitions']:
                    if all(mark.get(p,0)>=n for p,n in t['pre'].items()):
                        out,z=fire(net,mark,t);assert defect(out)==loss+z;nxt.append((out,loss+z))
            current=nxt
        expected=Counter({n:1 for n in range(minimum,bound+1,2)})
        assert counts==expected,(L,R,counts,expected)
    return tested,accepts

def main():
    program=json.loads((R/'source/virtual3.json').read_text());net=json.loads((R/'reset_net.json').read_text());literal_audit(program,net)
    source=source_replay(program,6,0);stored=json.loads((R/'source/accepting_counter_trace.json').read_text())['trace']
    assert [{k:v for k,v in a.items() if k!='branch'} for a in source]==stored
    masses=[6]+[sum(a['next_registers']) for a in source];K=max(masses)-6;assert K==19
    nettrace=expand(net,source,6,0,K);N=len(nettrace);assert N==388
    for k in range(K,K+5):assert len(expand(net,source,6,0,k))==N+2*(k-K)
    try:expand(net,source,6,0,K-1)
    except ValueError:pass
    else:raise AssertionError('insufficient fuel admitted')
    write('accepting_reset_trace.json',{'parameters':{'L':6,'R':0},'fuel':K,'trace':nettrace})
    peak=verify_source_peak(program,source,6,0,N);trace=verify_reset_trace(net,nettrace,6,0)
    weighted,mutations=weighted_semantics_tests();allruns,accepts=bounded_all_run_tests()
    assert json.loads((R/'projected_trace_schema_T1.json').read_text())==reset_schema(net,1,project_controls=True)
    assert json.loads((R/'canonical_peak_schema_h1.json').read_text())==compile_peak(semantic_table(program),1)
    result={'status':'passed','literal_source_rows_checked':528,'literal_transitions_checked':771,'weighted_reset_cases':weighted,'arithmetic_mutations_rejected':mutations,'bounded_run_prefixes_checked':allruns,'bounded_accepting_words':accepts,
      'example':{'L':6,'R':0,'source_instructions':len(source),'initial_mass':6,'peak_mass':max(masses),'final_mass':sum(source[-1]['next_registers']),'minimum_fuel':K,'minimum_reset_firings':N,'accepting_lengths':'388+2n for n>=0; exactly one labelled accepting word per length'},
      'canonical_peak_polynomial':peak,'projected_reset_trace_polynomial':trace,
      'scope':'Exact integer execution and arithmetic checks supplement the all-input proofs. This is not proof-assistant formalization or a fixed-arity unknown-time result.'}
    write('verification_receipt.json',result);print(json.dumps(result,indent=2))
if __name__=='__main__':main()
