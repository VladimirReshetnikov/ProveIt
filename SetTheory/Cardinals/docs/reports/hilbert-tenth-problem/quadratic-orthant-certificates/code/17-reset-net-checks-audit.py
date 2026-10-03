#!/usr/bin/env python3
"""Independent structural/arithmetic audit. No project implementation imports.
Reads audited JSON artifacts only and writes results in this directory.
"""
from pathlib import Path
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product
import json, hashlib, os, argparse
A=Path(__file__).resolve().parent
_parser=argparse.ArgumentParser(description=__doc__)
_parser.add_argument('packet_root', nargs='?', default=os.environ.get('RESET_NET_PACKET_ROOT', str(A.parent)), help='Reset-net packet root; defaults to RESET_NET_PACKET_ROOT or the parent of this script directory')
R=Path(_parser.parse_args().packet_root).expanduser().resolve()
if not (R/'reset_net.json').is_file():
    _parser.error('packet_root must contain reset_net.json')
load=lambda name:json.loads((R/name).read_text())
P=load('source/virtual3.json'); net=load('reset_net.json')
PINNED_SOURCE_SHA256='24c771db50dc621068e470227802c2710a4531ce2e7ad3703a5cdb6b0543bbcf'
assert hashlib.sha256((R/'source/virtual3.json').read_bytes()).hexdigest()==PINNED_SOURCE_SHA256, 'Packaged source differs from audited source pin'
assert P['registers']==['L','R','T']
rows=P['rows']; controls=list(rows)+['HALT','START','CLEAN_R','CLEAN_T','DRAIN','DONE']
places=['L','R','T','reserve','budget']+['q:'+q for q in controls]
assert net['places']==places and len(set(places))==539
assert len(rows)==528 and Counter(r[0] for r in rows.values())=={'ADD':295,'SUB':233}
assert net['parameters']==['L','R']
assert net['initial_affine']=={'L':{'L':1},'R':{'R':1},'budget':{'L':1,'R':1},'q:START':{'constant':1}}
assert net['target']=={'q:DONE':1}
assert net['data_places']==places[:5] and net['control_places']==places[5:]
assert net['controls']==controls
expected=[]
def tr(n,q,z,a=None,b=None,res=(),kind=None):
    expected.append((n,{'q:'+q:1,**(a or {})},{'q:'+z:1,**(b or {})},list(res),q,z,kind or n))
tr('pump','START','START',b={'reserve':1,'budget':1})
tr('enter','START',P['entry'])
branches=[]; codes={q:i for i,q in enumerate(list(rows)+['HALT'])}
for q,row in rows.items():
    op,r,*dst=row;p=P['registers'][r]
    if op=='ADD':
        tr(q+':inc',q,dst[0],{'reserve':1},{p:1},kind='INC')
        branches.append((codes[q],codes[dst[0]],r,'inc'))
    else:
        tr(q+':pos',q,dst[0],{p:1},{'reserve':1},kind='SUB_POS')
        tr(q+':zero',q,dst[1],res=[p],kind='SUB_ZERO')
        branches.extend([(codes[q],codes[dst[0]],r,'pos'),(codes[q],codes[dst[1]],r,'zero')])
phases=['HALT','CLEAN_R','CLEAN_T','DRAIN']
for i,p in enumerate(P['registers']):
    tr('clean_'+p,phases[i],phases[i],{p:1},{'reserve':1},kind='CLEAN')
    tr('advance_'+p,phases[i],phases[i+1],kind='ADVANCE')
tr('drain','DRAIN','DRAIN',{'reserve':1,'budget':1})
tr('finish','DRAIN','DONE')
actual=[tuple(t[k] for k in ['name','pre','post','reset','source_control','target_control','kind']) for t in net['transitions']]
assert actual==expected and len(actual)==len({x[0] for x in actual})==771
assert all(set(a)|set(b)|set(z)<=set(places) for n,a,b,z,*_ in actual)
assert sum(len(t[1]) for t in actual)==sum(len(t[2]) for t in actual)==1304
assert sum(len(t[3]) for t in actual)==233
assert all(w==1 for t in actual for d in t[1:3] for w in d.values())
assert all(sum(v for p,v in t[k].items() if p.startswith('q:'))==1 for t in actual for k in (1,2))
assert all(not any(p.startswith('q:') for p in t[3]) for t in actual)
byname={t['name']:i for i,t in enumerate(net['transitions'])}
def fire(mark,t):
    if any(mark.get(p,0)<v for p,v in t['pre'].items()):return None
    out={p:mark.get(p,0)-t['pre'].get(p,0) for p in places}
    loss=sum(out[p] for p in t['reset'])
    for p in t['reset']:out[p]=0
    for p,v in t['post'].items():out[p]+=v
    return {p:v for p,v in out.items() if v},loss
def deficit(m):return m.get('budget',0)-sum(m.get(p,0) for p in ['L','R','T','reserve'])
def source_run(L,R,limit=100000):
    q=P['entry'];x=[L,R,0];trace=[]
    while q!='HALT':
        assert len(trace)<limit
        old=x[:];op,r,*dst=rows[q]
        if op=='ADD':x[r]+=1;z=dst[0];suffix='inc'
        elif x[r]>0:x[r]-=1;z=dst[0];suffix='pos'
        else:z=dst[1];suffix='zero'
        trace.append((q,old,z,x[:],q+':'+suffix));q=z
    return trace
src=source_run(6,0);h=len(src);B=6;H=sum(src[-1][3]);M=max([B]+[sum(s[3]) for s in src]);K=M-B
assert (h,B,H,M,K)==(328,6,11,25,19)
def expected_word(k):
    names=['pump']*k+['enter']+[x[4] for x in src]
    for p,n in zip(P['registers'],src[-1][3]):names+=['clean_'+p]*n+['advance_'+p]
    names+=['drain']*(B+k)+['finish'];return names
for k in range(K,K+12):
    mark={'L':6,'budget':6,'q:START':1}
    for name in expected_word(k):
        result=fire(mark,net['transitions'][byname[name]]);assert result is not None
        mark,loss=result;assert loss==deficit(mark)==0
    assert mark==net['target'] and len(expected_word(k))==h+H+B+2*k+5
for k in range(K):
    mark={'L':6,'budget':6,'q:START':1}
    for name in expected_word(k):
        out=fire(mark,net['transitions'][byname[name]])
        if out is None:break
        mark,loss=out
    else:raise AssertionError('insufficient pump accepted')
rt=load('accepting_reset_trace.json');assert [x['name'] for x in rt['trace']]==expected_word(K)
mark={'L':6,'budget':6,'q:START':1};losses=0
for j,r in enumerate(rt['trace']):
    assert r['step']==j and {p:v for p,v in r['old'].items() if v}==mark
    t=net['transitions'][r['transition']];assert t['name']==r['name']
    mark,loss=fire(mark,t);losses+=loss
    assert (r['new'],r['reset_loss'],r['cumulative_loss'])==(mark,loss,losses)
    assert deficit(mark)==losses
assert mark==net['target'] and len(rt['trace'])==388
# Wrong zero resets from legal prefixes strictly increase the irreversible deficit.
false_reset_cases=0
for r in rt['trace']:
    t=net['transitions'][r['transition']]
    if t['kind']=='SUB_POS':
        bad=net['transitions'][byname[t['source_control']+':zero']]
        out,loss=fire(r['old'],bad)
        assert loss>0 and deficit(out)==loss
        false_reset_cases+=1
# Advancing too soon leaves a stranded positive counter; premature finishing strands reserve/budget.
premature_cleanup=0
for r in rt['trace']:
    t=net['transitions'][r['transition']]
    if t['kind']=='CLEAN':
        p=next(p for p in P['registers'] if t['pre'].get(p))
        out,loss=fire(r['old'],net['transitions'][byname['advance_'+p]])
        assert out[p]>0 and deficit(out)==0
        start=phases.index(t['target_control'])+1
        later=set(phases[start:])|{'DONE'}
        assert all(not(t['pre'].get(p) or t['post'].get(p) or p in t['reset']) for t in net['transitions'] if t['source_control'] in later)
        premature_cleanup+=1
# Expand every declared affine form into an independent coefficient map.
def lin(terms):
    out=Counter()
    for k,v in terms:out[k]+=v
    return {k:v for k,v in out.items() if v}
def expand(packet,a):
    terms=[(('constant',),a['constant'])]
    for f,c in a['forms']:terms += [(('v',i),c*k) for i,k in packet['linear_forms'][f]]
    terms += [(('v',i),c) for i,c in a['variables']]
    terms += [(('p',p),c) for p,c in a['parameters']]
    return lin(terms)
def expect_square(packet,name,terms):
    got=next(x['affine'] for x in packet['affine_squares'] if x['name']==name)
    assert expand(packet,got)==lin(terms),name
V=lambda i:('v',i); C=('constant',); PARAM=lambda p:('p',p)
def fg(packet,name,mult=1):return [(V(i),c*mult) for i,c in packet['linear_forms'][name]]
# Source + canonical peak h=1 export.
cp=load('canonical_peak_schema_h1.json');n=len(branches);assert n==761
layout=[];base_next=n
for q,z,r,op in branches:
    bs=[]
    for i in range(3):
        if op=='zero' and i==r:bs.append(None)
        else:bs.append(base_next);base_next+=1
    layout.append(bs)
assert base_next==2811 and cp['variables']['count']==2813
sf={'E:0':[[r,1] for r in range(n)],'Q:0':[[b,q] for b,(q,z,r,op) in enumerate(branches) if q],'D:0':[[b,z] for b,(q,z,r,op) in enumerate(branches) if z]}
for i in range(3):
    old=[];new=[]
    for b,(q,z,r,op) in enumerate(branches):
        if layout[b][i] is not None:old.append([layout[b][i],1]);new.append([layout[b][i],1])
        if i==r and op=='pos':old.append([b,1])
        if i==r and op=='inc':new.append([b,1])
    sf['OLD%d:0'%i]=old;sf['NEW%d:0'%i]=new
assert cp['linear_forms']==sf
expect_square(cp,'onehot:0',fg(cp,'E:0')+[(C,-1)])
expect_square(cp,'control:0',fg(cp,'Q:0')+[(C,-codes[P['entry']])])
for i,p in enumerate(['L','R',None]):expect_square(cp,'counter%d:0'%i,fg(cp,'OLD%d:0'%i)+([] if p is None else [(PARAM(p),-1)]))
expect_square(cp,'terminal',fg(cp,'D:0')+[(C,-codes['HALT'])])
expect_square(cp,'peak:0',[(PARAM('L'),1),(PARAM('R'),1),(V(2811),1),(V(2812),-1)]+sum([fg(cp,'NEW%d:0'%i,-1) for i in range(3)],[]))
expect_square(cp,'minimum_reset_duration',[(PARAM('N'),1),(PARAM('L'),1),(PARAM('R'),1),(V(2812),-2),(C,-6)]+sum([fg(cp,'NEW%d:0'%i,-3) for i in range(3)],[]))
for b,term in enumerate(cp['quadratic_products'][:-1]):
    assert expand(cp,term['left'])=={V(i):1 for i in range(n) if i!=b}
    assert expand(cp,term['right'])=={V(i):1 for i in [b]+[x for x in layout[b] if x is not None]}
assert expand(cp,cp['quadratic_products'][-1]['left'])=={V(2811):1}
assert expand(cp,cp['quadratic_products'][-1]['right'])=={V(2812):1}
assert len(cp['affine_squares'])==8 and len(cp['quadratic_products'])==762
# Generic reset trace, projected control T=1 export.
pk=load('projected_trace_schema_T1.json');m=len(actual);d=5;stride=m*(d+1)
assert pk['variables']['count']==stride==4626
qcode={q:i for i,q in enumerate(net['control_places'])}
f={'E:0':[[r,1] for r in range(m)]}
f['Q:0']=[[r,qcode['q:'+t['source_control']]] for r,t in enumerate(net['transitions']) if qcode['q:'+t['source_control']]]
f['D:0']=[[r,qcode['q:'+t['target_control']]] for r,t in enumerate(net['transitions']) if qcode['q:'+t['target_control']]]
for i,p in enumerate(net['data_places']):
    old=[];new=[]
    for r,t in enumerate(net['transitions']):
        b=m+r*d+i;old.append([b,1])
        if p in t['pre']:old.append([r,t['pre'][p]])
        if p not in t['reset']:new.append([b,1])
        if p in t['post']:new.append([r,t['post'][p]])
    f['OLD%d:0'%i]=old;f['NEW%d:0'%i]=new
assert pk['linear_forms']==f
expect_square(pk,'onehot:0',fg(pk,'E:0')+[(C,-1)])
expect_square(pk,'control:0',fg(pk,'Q:0')+[(C,-qcode['q:START'])])
for i,p in enumerate(net['data_places']):
    init=net['initial_affine'].get(p,{})
    expect_square(pk,'place:0:'+p,fg(pk,'OLD%d:0'%i)+[(PARAM(q),-c) for q,c in init.items()])
    expect_square(pk,'terminal:'+p,fg(pk,'NEW%d:0'%i))
expect_square(pk,'terminal:control',fg(pk,'D:0')+[(C,-qcode['q:DONE'])])
for r,term in enumerate(pk['quadratic_products']):
    assert expand(pk,term['left'])=={V(i):1 for i in range(m) if i!=r}
    assert expand(pk,term['right'])=={V(i):1 for i in [r]+[m+r*d+i for i in range(d)]}
assert len(pk['affine_squares'])==13 and len(pk['quadratic_products'])==771
# Independently verify ALL coordinates of stored natural witnesses by reconstruction.
rw=load('accepting_reset_witness.json');want={}
for j,r in enumerate(rt['trace']):
    off=j*stride;b=r['transition'];t=net['transitions'][b];want[off+b]=1
    for i,p in enumerate(net['data_places']):
        val=r['old'].get(p,0)-t['pre'].get(p,0)
        assert val>=0
        if val:want[off+m+b*d+i]=val
assert dict(rw['nonzero_coordinates'])==want and rw['variable_count']==stride*388==1794888
sw=load('accepting_peak_witness.json');want={};lastM=B;lastv=0
bi={(q,op):b for b,(q,z,r,op) in enumerate(branches)}
for j,(q,old,z,new,name) in enumerate(src):
    op=name.rsplit(':',1)[1];b=bi[codes[q],op];want[j*2811+b]=1
    for i,idx in enumerate(layout[b]):
        val=old[i]-(op=='pos' and branches[b][2]==i)
        if idx is None:assert val==0
        elif val:want[j*2811+idx]=val
    S=sum(new);u=max(S-lastM,0);v=max(lastM-S,0)
    if u:want[2811*h+2*j]=u
    if v:want[2811*h+2*j+1]=v
    assert sum(old)+lastv+u-S-v==0 and u*v==0
    lastM=max(lastM,S);lastv=v
assert dict(sw['nonzero_coordinates'])==want and sw['variable_count']==2813*h==922664
assert sw['parameters']=={'L':6,'R':0,'N':388}
assert 388-h-3*H+B-2*lastv-5==0
# The strong selectors reject nonintegral mixtures even over R_+.
fractional_rejections=0
for e in (Fraction(1,7),Fraction(1,3),Fraction(1,2),Fraction(2,3),Fraction(6,7)):
    for b in (0,Fraction(1,5),1,3):
        assert (1-e)*(e+b)>0;fractional_rejections+=1
# Peak complementarity has unique (necessarily integer) solution for integer M,S.
peak_cases=0
for peak,cur in product(range(8),repeat=2):
    solutions=[]
    for u,v in product([Fraction(i,2) for i in range(17)],repeat=2):
        if (peak+u-cur-v)**2+u*v==0:solutions.append((u,v))
    assert solutions==[(max(cur-peak,0),max(peak-cur,0))];peak_cases+=1
# Natural z is essential for the all-duration arithmetic progression.
Tmin=388
assert (389-Tmin-2*Fraction(1,2))**2==0
assert all((389-Tmin-2*z)**2>0 for z in range(20))
for z in range(20):assert Tmin+2*z in [len(expected_word(K+j)) for j in range(20)]
# Local symbolic deficit check against every transition, on many enabled states.
# Control marking has a token at that transition's source, independently of reachability.
deficit_checks=0
for t in net['transitions']:
    for vals in product(range(3),repeat=5):
        mark={p:v for p,v in zip(net['data_places'],vals) if v};mark['q:'+t['source_control']]=1
        out=fire(mark,t)
        if out is None:continue
        new,loss=out;assert deficit(new)-deficit(mark)==loss
        deficit_checks+=1
hashes={name:hashlib.sha256((R/name).read_bytes()).hexdigest() for name in ['source/virtual3.json','reset_net.json','canonical_peak_schema_h1.json','projected_trace_schema_T1.json','accepting_reset_trace.json','accepting_peak_witness.json','accepting_reset_witness.json']}
result={'status':'PASS','source_rows':528,'net_places':539,'net_transitions':771,'ordinary_arcs':2608,'reset_arcs':233,'literal_source_equality':True,'pinned_source_sha256':PINNED_SOURCE_SHA256,'all_export_coefficients_independently_checked':True,'example':{'source_steps':h,'initial_mass':B,'final_mass':H,'peak':M,'minimum_pump':K,'shortest_duration':388,'accepting_lengths':'388+2z, z in N'},'accepted_pump_values_checked':12,'insufficient_pump_values_rejected':19,'wrong_zero_transitions_checked':false_reset_cases,'premature_cleanup_cases':premature_cleanup,'transition_deficit_checks':deficit_checks,'fractional_gate_rejections':fractional_rejections,'half_integer_peak_grid_cases':peak_cases,'stored_peak_witness_all_coordinates_verified':922664,'stored_reset_witness_all_coordinates_verified':1794888,'all_duration_parity_warning':'Natural padding z required. z=1/2 admits N=389 over nonnegative reals.','sha256':hashes,'scope':'Independent literal export and exact arithmetic checks supplement the all-input proof; not proof-assistant formalization.'}
(A/'AUDIT_RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
