#!/usr/bin/env python3
"""Independent adversarial tests for compact cleanup certificates."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import importlib.util
from copy import deepcopy
from itertools import product
import hashlib,json
HERE=Path(__file__).resolve().parent
SUBJECT=HERE.parent

def load(name,path):
    s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m
ct=load('audit_ct_subject',SUBJECT/'clean_targets.py')
ck=load('audit_ck_subject',SUBJECT/'check_clean_targets.py')
ref=load('audit_reference',HERE/'audit_actual_ca.py')
I,M=ct.Instruction,ct.Machine

class Stats:
    good=0; mutations=0; syntax=0; exhausted=0
stats=Stats()

def rejects(f,category='mutations'):
    try:f()
    except (ValueError,TypeError,KeyError,AssertionError):
        setattr(stats,category,getattr(stats,category)+1);return
    raise AssertionError('invalid item accepted')

def reference_trace(m,initial,N):
    rm=ref.core.Machine(m.states,m.halt,tuple(ref.I(i.source,i.target,i.operation,i.counter) for i in m.instructions))
    cm=ref.wrapped(rm.states,rm.halt,rm.instructions,initial)
    tr,status=ref.execute(cm,'F:'+initial,N,30)
    assert status=='halt'
    return tr

def test_success(m,initial,h,N,model,mode):
    tin=None if mode=='none' else {'mode':'free','name':'T'}
    c=ct.export_clean_certificate(m,initial,h,{'mode':'fixed_raw','N':N},tin,model)
    w=ct.make_clean_witness(c);out=ck.check(c,w)
    tr=reference_trace(m,initial,N);scale=4 if model=='phase-radius-one' else 1
    assert [(r['state'],r['N'],r['microtime']) for r in out['cleaned_source_trace']]==[(q,n,t*scale) for q,n,t in tr]
    assert out['exact_target_N']==N and c['exact_target_N']==c['initial_N']
    assert len(c['variables'])==2*len(m.branches())*h+(mode!='none')
    assert c['ledger']['core_squares']==3*h+1 and c['ledger']['product_slots']==len(m.branches())*h
    if mode=='free':assert w['T']==out['physical_time']
    c['expanded_polynomial']=ct.core.expand_polynomial(c);assert ck.check(c,w)['physical_time']==out['physical_time']
    # Fixed requested clock must agree exactly, with no free output variable.
    fixed=ct.export_clean_certificate(m,initial,h,{'mode':'fixed_raw','N':N},{'mode':'fixed','value':out['physical_time']},model)
    fw=ct.make_clean_witness(fixed);ck.check(fixed,fw)
    assert 'T' not in fw
    badtime=ct.export_clean_certificate(m,initial,h,{'mode':'fixed_raw','N':N},{'mode':'fixed','value':out['physical_time']+1},model)
    rejects(lambda:ct.make_clean_witness(badtime))
    rejects(lambda:ck.check(badtime,fw))
    stats.good+=1
    return c,w

def main():
    snapshots={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [SUBJECT/'clean_targets.py',SUBJECT/'check_clean_targets.py']}
    subjects=[(M(('q',),'q',()),'q',0,[1,5]),
              (M(('s','h'),'h',(I('s','h','inc',0),)),'s',1,[1,5]),
              (M(('s','h'),'h',(I('s','h','zero',1),)),'s',1,[1,2,5]),
              (M(('s','a','h'),'h',(I('s','a','inc',1),I('a','h','dec',0))),'s',2,[2,10]),
              (M(('F:x','B:x','H'),'H',(I('F:x','B:x','nop'),I('B:x','H','nop'))),'F:x',2,[1])]
    for m,initial,h,ns in subjects:
        for N,model,mode in product(ns,('native','spatial-radius-one','phase-radius-one'),('none','free')):
            c,w=test_success(m,initial,h,N,model,mode)
    m=M(('s','h'),'h',(I('s','h','zero',1),))
    c,w=test_success(m,'s',1,5,'native','free')
    mut=[]
    def changed(path,value):
        a=deepcopy(c);p=a
        for k in path[:-1]:p=p[k]
        p[path[-1]]=value;mut.append((path,a))
    for path,value in [
        (['exact_target_N'],{'':1}),(['initial_N'],{'':1}),(['exact_target_state'],'F:h'),
        (['cleaned_initial_state'],'B:s'),(['cleaned_source_horizon'],3),(['clock_scale'],4),
        (['clock_scale'],True),(['model'],'phase-radius-one'),(['domain'],'integers'),
        (['physical_time'],{'':1}),(['cleaned_machine','instructions',1,'operation'],'positive'),
        (['cleaned_machine','instructions',2,'target'],'H'),(['cleaned_machine','instructions',3,'source'],'B:h'),
        (['cleaned_machine','states',0],'x'),(['cleaned_machine','halt'],'F:h'),
        (['source_ledger','expanded_branches'],1),(['cleaned_source_ledger','expanded_branches'],5),
        (['ledger','core_variables'],8),(['ledger','core_squares'],7),(['ledger','maximum_degree'],1),
        (['time_spec','name'],'x'),(['time_spec','mode'],'fixed'),
        (['squares',0,'affine',''],0),(['products',0,'right'],{}),
        (['forward_certificate','clock_scale'],4),(['forward_certificate','initial_state'],'h'),
        (['forward_certificate','horizon'],0),(['forward_certificate','machine','instructions',0,'operation'],'positive'),
        (['forward_certificate','branches',0,'residue'],0),(['forward_certificate','steps',0,0,'old'],{'':5}),
        (['expanded_polynomial',0,'coefficient'],100),
    ]:changed(path,value)
    for path,d in mut:rejects(lambda d=d:ck.check(d,w))
    for key in w:
        v=dict(w);v[key]+=1;rejects(lambda v=v:ck.check(c,v))
        v=dict(w);v[key]=True;rejects(lambda v=v:ck.check(c,v))
        v=dict(w);v[key]=-1;rejects(lambda v=v:ck.check(c,v))
        v=dict(w);v.pop(key);rejects(lambda v=v:ck.check(c,v))
    v=dict(w);v['unexpected']=0;rejects(lambda:ck.check(c,v))
    # Unsupported original machine syntax and freshness are rejected before generation.
    syntax=[(M(('s','a','h'),'h',(I('s','a','zero'),I('a','s','inc'),I('s','h','positive'))),'s'),
            (M(('s','a','h'),'h',(I('a','s','positive'),I('s','h','nop'))),'s'),
            (M(('s','h'),'h',(I('s','h','inc'),I('s','h','dec'))),'s'),
            (M(('s','a','h'),'h',(I('s','h','inc'),I('a','h','dec'))),'s'),
            (M(('s','a','h'),'h',(I('s','a','zero',0),I('s','h','positive',1))),'s'),
            (M(('s','a','h'),'h',(I('s','h','zero',0),I('a','h','positive',1))),'s'),
            (M(('s','h'),'h',(I('s','h','nop'),I('h','s','nop'))),'s'),
            (M(('s','h'),'h',(I('s','h','nop'),)),'missing')]
    for sm,q0 in syntax:rejects(lambda sm=sm,q0=q0:ct.clean_source(sm,q0),'syntax')
    # The checker must reject independently even when given a valid forward certificate
    # for the structurally nonfresh, actually returning source.
    bad=syntax[0][0]
    f=ct.core.export_certificate(bad,'s',3,{'mode':'fixed_raw','N':1});fw=ct.core.make_witness(f)
    d=deepcopy(c);d['forward_certificate']=f;d['variables']=list(fw)
    rejects(lambda:ck.check(d,fw),'syntax')
    for model in ('',0,None,'radius-one'):
        rejects(lambda model=model:ct.export_clean_certificate(m,'s',1,{'mode':'fixed_raw','N':1},model=model),'syntax')
    for spec in ({'mode':'free','name':'e_0_0'},{'mode':'free','name':''},{'mode':'fixed','value':True},
                 {'mode':'fixed','value':-1},{'mode':'fixed','value':1,'x':0},{'mode':'free','name':3}):
        rejects(lambda spec=spec:ct.export_clean_certificate(m,'s',1,{'mode':'fixed_raw','N':1},spec),'syntax')
    # Exhaustively enumerate the small natural box for B=2, h=1. Correct active
    # branch witnesses fit the box. Disabled raw multiples of 3 have no zeros.
    for N in (1,2,3,4,5,6):
        e=ct.export_clean_certificate(m,'s',1,{'mode':'fixed_raw','N':N})
        zeros=[]
        for values in product(range(4),repeat=4):
            nw=dict(zip(e['variables'],values));stats.exhausted+=1
            if ct.core.polynomial_value(e,nw)==0:
                ck.check(e,nw);zeros.append(nw)
        if N%3==0:assert not zeros
        else:assert zeros==[ct.make_clean_witness(e)]
    # Free raw and bounded counter interfaces preserve the compact core ledger.
    simple=subjects[1][0]
    for input_spec,inputs,N in [({'mode':'free_raw','name':'x'},{'x':4},5),
         ({'mode':'bounded_counters','A':2,'B':2,'a':None,'b':None},{'input_a':1,'input_b':2},18)]:
        e=ct.export_clean_certificate(simple,'s',1,input_spec,{'mode':'free','name':'t'})
        ew=ct.make_clean_witness(e,inputs);er=ck.check(e,ew)
        assert er['exact_target_N']==N and e['ledger']['core_variables']==2
        if input_spec['mode']=='bounded_counters':assert e['ledger']['loader_variables']==9 and e['ledger']['loader_squares']==3
    assert snapshots=={p:hashlib.sha256((SUBJECT/p).read_bytes()).hexdigest() for p in snapshots},'subject changed during audit'
    out={'status':'PASS','successful_model_interface_cases':stats.good,'rejected_mutations':stats.mutations,
         'rejected_syntax_or_api_cases':stats.syntax,'exhaustive_natural_assignments':stats.exhausted,
         'subject_sha256':snapshots}
    (HERE/'certificate-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
