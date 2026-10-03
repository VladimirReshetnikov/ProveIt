#!/usr/bin/env python3
"""Independent audit of literal JSON; imports no producer modules and modifies no inputs."""
import json, hashlib, argparse
from collections import Counter, defaultdict, deque
from pathlib import Path
OUT=Path(__file__).resolve().parent
_parser=argparse.ArgumentParser(description=__doc__)
_default=OUT.parent
_parser.add_argument('--base',type=Path,default=_default,help='Root of the reset-net packet, containing source/ and shared-reset-arcs/.')
BASE=_parser.parse_args().base.resolve()
HASH={}
def read(p):
    b=p.read_bytes(); HASH[str(p.relative_to(BASE))]=hashlib.sha256(b).hexdigest(); return json.loads(b)
def sparse(m):return {p:v for p,v in m.items() if v}
def fire(t,m):
    if any(m.get(p,0)<v for p,v in t['pre'].items()):return None
    n=m.copy()
    for p,v in t['pre'].items():n[p]=n.get(p,0)-v
    loss=sum(n.get(p,0) for p in t['reset'])
    for p in t['reset']:n[p]=0
    for p,v in t['post'].items():n[p]=n.get(p,0)+v
    assert all(type(v) is int and v>=0 for v in n.values())
    return sparse(n),loss
def load(net,params):return sparse({p:sum(c*(1 if k=='constant' else params[k]) for k,c in a.items()) for p,a in net['initial_affine'].items()})
def ledger(net):
    t=net['transitions'];a=sum(map(lambda z:len(z['pre']),t));b=sum(map(lambda z:len(z['post']),t));c=sum(map(lambda z:len(z['reset']),t))
    return dict(places=len(net['places']),data_places=len(net['data_places']),resource_places=len(net['resource_places']),marker_places=len(net['marker_places']),control_places=len(net['control_places']),transitions=len(t),ordinary_input_arcs=a,ordinary_output_arcs=b,ordinary_arcs=a+b,reset_arcs=c,all_arcs=a+b+c,max_input_weight=max(v for z in t for v in z['pre'].values()),max_output_weight=max(v for z in t for v in z['post'].values()),max_total_incidence_transition=max(len(z['pre'])+len(z['post'])+len(z['reset']) for z in t),distinct_reset_places=sorted({p for z in t for p in z['reset']}),transition_kinds=dict(Counter(z['kind'] for z in t)))
def assert_arcs(t,pre,post,reset=()):
    assert t['pre']==pre and t['post']==post and t['reset']==list(reset),t['name']
def structure(label):
    bp=BASE if label=='three-counter' else BASE/'two-counter'; sp=BASE/'shared-reset-arcs'/label
    d=read(bp/'reset_net.json');n=read(sp/'reset_net.json');s=read(bp/'source'/('virtual3.json' if label=='three-counter' else 'literal2.json'))
    rows=s['rows'];r=len(s['registers']);I=sum(row[0]=='ADD' for row in rows.values());S=len(rows)-I;q=len(rows)
    assert len(set(n['places']))==len(n['places']);assert len(set(t['name'] for t in n['transitions']))==len(n['transitions'])
    places=set(n['places']);ctrl=set(n['control_places']);marker=set(n['marker_places']);regs=s['registers'];oldctrl=set(d['control_places'])
    assert set(n['data_places']).isdisjoint(ctrl) and set(n['data_places'])|ctrl==places
    assert n['resource_places']==regs+['reserve','budget'];assert n['counter_places']==regs;assert n['direct_control_places']==d['control_places']
    assert n['parameters']==d['parameters'] and n['initial_affine']==d['initial_affine'] and n['target']==d['target']=={'q:DONE':1}
    expected_loader=({'L':{'L':1},'R':{'R':1},'budget':{'L':1,'R':1},'q:START':{'constant':1}} if r==3 else {'A':{'raw_A':1},'budget':{'raw_A':1},'q:START':{'constant':1}})
    assert n['initial_affine']==expected_loader
    by={t['name']:t for t in n['transitions']};db={t['name']:t for t in d['transitions']};zmap={};marker_counter={};expansion={};control_index=defaultdict(list)
    for lab,row in rows.items():
        op,i,*ds=row;p=regs[i];qc='q:'+lab
        if op=='ADD':
            t=by[lab+':inc'];assert_arcs(t,{qc:1,'reserve':1},{'q:'+ds[0]:1,p:1});assert t==db[t['name']]
        else:
            pos=by[lab+':pos'];assert_arcs(pos,{qc:1,p:1},{'q:'+ds[0]:1,'reserve':1});assert pos==db[pos['name']]
            z=db[lab+':zero'];assert_arcs(z,{qc:1},{'q:'+ds[1]:1},[p]);gate='q:SHARED_GATE_'+p;post='q:SHARED_POST_'+p;mark='marker:'+lab
            dispatch=by[lab+':dispatch'];ret=by[lab+':return'];reset=by['shared_reset_'+p]
            assert_arcs(dispatch,{qc:1},{gate:1,mark:1});assert_arcs(reset,{gate:1},{post:1},[p]);assert_arcs(ret,{post:1,mark:1},{'q:'+ds[1]:1})
            zmap[lab]=(p,mark,dispatch,reset,ret);marker_counter[mark]=p;expansion[z['name']]=[dispatch['name'],reset['name'],ret['name']]
    assert_arcs(by['pump'],{'q:START':1},{'q:START':1,'reserve':1,'budget':1})
    assert_arcs(by['enter'],{'q:START':1},{'q:'+s['entry']:1})
    cleanup=['q:HALT']+['q:CLEAN_'+p for p in regs[1:]]+['q:DRAIN']
    for i,p in enumerate(regs):
        assert_arcs(by['clean_'+p],{cleanup[i]:1,p:1},{cleanup[i]:1,'reserve':1})
        assert_arcs(by['advance_'+p],{cleanup[i]:1},{cleanup[i+1]:1})
    assert_arcs(by['drain'],{'q:DRAIN':1,'reserve':1,'budget':1},{'q:DRAIN':1})
    assert_arcs(by['finish'],{'q:DRAIN':1},{'q:DONE':1})
    assert not any('q:DONE' in t['pre'] for t in n['transitions'])
    for name,t in db.items():
        if t['kind']!='SUB_ZERO':assert by[name]==t;expansion[name]=[name]
    assert n['zero_expansion']==expansion
    expected_names={name for name,t in db.items() if t['kind']!='SUB_ZERO'}|{lab+ending for lab in zmap for ending in [':dispatch',':return']}|{'shared_reset_'+p for p in regs}
    assert set(by)==expected_names and set(marker_counter)==marker
    assert places-set(d['places'])==marker|{'q:SHARED_'+kind+'_'+p for kind in ['GATE','POST'] for p in regs}
    assert set(d['places'])<=places
    # All-transition checks of the controller and per-counter pending-marker linear invariants.
    # L_i=sum_{tested(l)=i}marker_l-GATE_i-POST_i=0, in addition to sum control=1.
    invs=[]
    for p in regs:invs.append({**{m:1 for m,mp in marker_counter.items() if mp==p},'q:SHARED_GATE_'+p:-1,'q:SHARED_POST_'+p:-1})
    debt={p:-1 for p in regs};debt.update(reserve=-1,budget=1)
    for t in n['transitions']:
        assert set(t['pre'])|set(t['post'])|set(t['reset'])<=places
        assert all(type(v) is int and v==1 for v in list(t['pre'].values())+list(t['post'].values()))
        assert len(set(t['reset']))==len(t['reset'])
        assert not (ctrl|marker)&set(t['reset'])
        assert sum(t['pre'].get(p,0) for p in ctrl)==sum(t['post'].get(p,0) for p in ctrl)==1
        cps=[p for p in t['pre'] if p in ctrl];control_index[cps[0]].append(t)
        assert t['source_control']==cps[0][2:] and t['target_control']==next(p[2:] for p in t['post'] if p in ctrl)
        for inv in invs:assert sum(inv.get(p,0)*v for p,v in t['pre'].items())==sum(inv.get(p,0)*v for p,v in t['post'].items())
        assert sum(debt.get(p,0)*v for p,v in t['pre'].items())==sum(debt.get(p,0)*v for p,v in t['post'].items())
        assert not t['reset'] or (t['kind']=='SHARED_RESET' and len(t['reset'])==1 and t['reset'][0] in regs)
    a=ledger(n);assert a==read(sp/'net_ledger.json')
    assert a['places']==q+4*r+S+5 and a['transitions']==I+3*S+3*r+4
    assert a['ordinary_arcs']==4*I+10*S+8*r+12 and a['reset_arcs']==r
    assert a['ordinary_input_arcs']==a['ordinary_output_arcs'] and a['max_total_incidence_transition']==4
    # Generic controller projection must retain markers as ordinary data.
    D=len(n['data_places']);T=len(n['transitions']);P=len(n['places'])
    cert={'controller_only_projection':{'witness_coefficient':(D+1)*T,'squares_N_coefficient':D+2,'squares_constant':D+1,'products_coefficient':T},'unprojected':{'witness_coefficient':(P+1)*T,'squares_N_coefficient':P+1,'squares_constant':P,'products_coefficient':T}}
    ctx=dict(net=n,direct=d,source=s,by=by,db=db,zmap=zmap,regs=regs,ctrl=ctrl,marker=marker,invs=invs,index=control_index,sp=sp,bp=bp,expansion=expansion)
    return ctx,dict(source_rows=q,ADD=I,SUB=S,registers=r,ledger=a,linear_invariants_checked_per_transition=1+r+1,trace_certificate_counts=cert)
def invariant(c,m,loss=0):
    assert sum(m.get(p,0) for p in c['ctrl'])==1
    for inv in c['invs']:assert sum(v*m.get(p,0) for p,v in inv.items())==0
    assert m.get('budget',0)-m.get('reserve',0)-sum(m.get(p,0) for p in c['regs'])==loss
    assert sum(m.get(p,0) for p in c['marker'])<=1

def adversarial(c):
    mismatches=premature=local_steps=0;ts=c['net']['transitions']; all_returns=[v[-1] for v in c['zmap'].values()]
    # Every SUB label, with true and false zero choices and arbitrary resource sizes.
    for lab,(p,marker,d,z,r) in c['zmap'].items():
        for value in [0,1,7]:
            m={'q:'+lab:1,p:value,'reserve':2,'budget':value+2};m=sparse(m);invariant(c,m)
            # A return cannot precede dispatch, including any same-counter return.
            for ret in all_returns:
                assert fire(ret,m) is None;premature+=1
            m,loss=fire(d,m);invariant(c,m,loss)
            en=[t for t in c['index']['q:SHARED_GATE_'+p] if fire(t,m) is not None]
            assert [t['name'] for t in en]==[z['name']]
            # Gate has no other outgoing transitions; source and cleanup require the absent control.
            for ret in c['index']['q:SHARED_POST_'+p]:
                assert fire(ret,m) is None;premature+=1
            m,newloss=fire(z,m);loss+=newloss;assert loss==value;invariant(c,m,loss)
            en=[]
            for ret in c['index']['q:SHARED_POST_'+p]:
                got=fire(ret,m)
                if ret['name']==r['name']:assert got is not None;en.append(ret)
                else:assert got is None;mismatches+=1
            assert len(en)==1
            m,newloss=fire(r,m);invariant(c,m,loss+newloss)
            assert m.get(p,0)==0 and not any(m.get(x,0) for x in c['marker'])
            assert fire(r,m) is None;premature+=1;local_steps+=3
    return dict(source_zero_labels_checked=len(c['zmap']),counter_values_tested=[0,1,7],macro_firings=local_steps,premature_or_repeated_returns_disabled=premature,mismatched_returns_disabled=mismatches)

def source_run(s,vals,maxsteps=10000):
    q=s['entry'];v=vals[:];out=[]
    while q!=s['halt']:
        assert len(out)<maxsteps
        op,i,*ds=s['rows'][q];old=v[:]
        if op=='ADD':v[i]+=1;dest=ds[0];suffix=':inc'
        elif v[i]:v[i]-=1;dest=ds[0];suffix=':pos'
        else:dest=ds[1];suffix=':zero'
        out.append((q+suffix,old,v[:],q,dest));q=dest
    return out

def decode(c,m):
    out={p:v for p,v in m.items() if p in c['direct']['places']}
    pending=[p for p in c['marker'] if m.get(p,0)]
    if pending:
        assert len(pending)==1 and m[pending[0]]==1
        lab=pending[0][7:];reg,mark,disp,reset,ret=c['zmap'][lab]
        q=disp['source_control'] if m.get('q:SHARED_GATE_'+reg,0) else ret['target_control']
        out['q:'+q]=1
    return sparse(out)

def replay_three(c):
    source=source_run(c['source'],[6,0,0]);assert len(source)==328
    Z=sum(x[0].endswith(':zero') for x in source);M=max(sum([6,0,0]),*(sum(x[2]) for x in source));F=sum(source[-1][2]);K=M-6
    assert (Z,M,F,K)==(29,25,11,19)
    def run(k):
        m=load(c['net'],{'L':6,'R':0});trace=[];loss=0;decoded=[]
        source_word=[x[0] for x in source]
        direct_word=['pump']*k+['enter']+source_word
        for p,v in zip(c['regs'],source[-1][2]):direct_word+=['clean_'+p]*v+['advance_'+p]
        direct_word+=['drain']*(6+k)+['finish']
        dmark=m.copy()
        for name in direct_word:
            oldt=c['db'][name];direct_result=fire(oldt,dmark)
            if direct_result is None:return dict(blocked=name,steps=len(trace),marking=m)
            dnew,dl=direct_result
            for wordname in c['expansion'][name]:
                t=c['by'][wordname];got=fire(t,m);assert got is not None
                new,lost=got;loss+=lost;invariant(c,new,loss)
                before,after=decode(c,m),decode(c,new)
                if t['kind'] in ['ZERO_DISPATCH','ZERO_RETURN']:assert before==after and lost==0
                else:assert fire(oldt,before)==(after,lost)
                trace.append(dict(name=wordname,old=m,new=new,reset_loss=lost,cumulative_loss=loss));m=new
            assert m==dnew;dmark=dnew;decoded.append(name)
        assert m==c['net']['target'] and loss==0
        return dict(length=len(trace),trace=trace,decoded=decoded)
    blocked=run(18);assert 'blocked' in blocked
    runs={k:run(k) for k in [19,20,21]};assert [runs[k]['length'] for k in runs]==[446,448,450]
    saved=read(c['sp']/'accepting_reset_trace_N446.json');mine=runs[19]['trace'];assert saved['length']==len(mine)
    for j,(a,b) in enumerate(zip(mine,saved['trace'])):
        assert all(a[k]==sparse(b[k]) if k in ['old','new'] else a[k]==b[k] for k in a)
        assert b['step']==j and c['net']['transitions'][b['transition']]['name']==a['name']
    assert saved['decoded_direct_word']==runs[19]['decoded']
    # Reachable premature cleanup/drain exits: skip a positive final R, then drain everything possible.
    idx=next(j for j,t in enumerate(mine) if t['name']=='clean_R');m=mine[idx]['old'];m,_=fire(c['by']['advance_R'],m);m,_=fire(c['by']['advance_T'],m)
    while fire(c['by']['drain'],m) is not None:m,_=fire(c['by']['drain'],m)
    m,_=fire(c['by']['finish'],m);assert m.get('q:DONE')==1 and m!=c['net']['target'];badcleanup=m
    di=next(j for j,t in enumerate(mine) if t['name']=='drain');earlyfinish,_=fire(c['by']['finish'],mine[di]['old']);assert earlyfinish.get('q:DONE')==1 and earlyfinish!=c['net']['target']
    # Reachable dishonest reset and bounded successor graph. Debt is a proved invariant, not bounded evidence alone.
    row=next(x for x in mine if x['name'].endswith(':pos') and x['old'].get(c['source']['registers'][c['source']['rows'][x['name'][:-4]][1]],0)>0)
    lab=row['name'][:-4];m=row['old'];loss=0
    for t in c['zmap'][lab][2:]:m,l=fire(t,m);loss+=l;invariant(c,m,loss)
    assert loss>0
    q=deque([(m,0)]);seen={tuple(sorted(m.items()))};edges=0
    while q:
        m,depth=q.popleft();assert m!=c['net']['target'];invariant(c,m,loss)
        if depth==14:continue
        cp=next(p for p in c['ctrl'] if m.get(p,0))
        for t in c['index'][cp]:
            got=fire(t,m)
            if got is None:continue
            new,extra=got;assert extra>=0
            # All these bounded descendants have no additional nonzero resets, but allow them if present.
            debt=new.get('budget',0)-new.get('reserve',0)-sum(new.get(p,0) for p in c['regs']);assert debt>=loss;invariant(c,new,debt)
            key=tuple(sorted(new.items()));edges+=1
            if key not in seen:seen.add(key);q.append((new,depth+1))
    return dict(source_steps=len(source),source_zero_steps=Z,peak=M,final_mass=F,minimum_fuel=K,lengths_replayed=[446,448,450],minimum_trace_fixture_exact=True,insufficient_fuel=blocked,premature_cleanup_DONE_marking=badcleanup,premature_finish_DONE_marking=earlyfinish,all_step_stuttering_projection_checked=True,dishonest_reset_loss=loss,wrong_reset_descendant_states=len(seen),wrong_reset_descendant_edges=edges),source

def schema_check(c,source=None):
    old=read(c['bp']/'canonical_peak_schema_h1.json');new=read(c['sp']/'canonical_peak_schema_h1.json');h=1
    assert old['variables']==new['variables'] and old['ledger']==new['ledger'] and old['quadratic_products']==new['quadratic_products']
    branches=[t for t in c['direct']['transitions'] if t['kind'] in ['INC','SUB_POS','SUB_ZERO']];zero_indices=[i for i,t in enumerate(branches) if t['kind']=='SUB_ZERO']
    assert new['linear_forms']==dict(old['linear_forms'],SOURCE_ZERO_COUNT=[[i,1] for i in zero_indices])
    assert len(old['affine_squares'])==len(new['affine_squares'])
    for a,b in zip(old['affine_squares'],new['affine_squares']):
        if a['name']=='minimum_reset_duration':
            expected=json.loads(json.dumps(a));expected['name']='minimum_shared_reset_duration';expected['affine']['forms'].append(['SOURCE_ZERO_COUNT',-2]);assert b==expected
        else:assert a==b
    r=len(c['regs']);b=len(branches);S=len(zero_indices);stride=(r+1)*b-S
    assert new['ledger']==dict(natural_witnesses=stride+2,affine_squares=r+5,quadratic_products=b+1,degree_at_most=2)
    out=dict(h1_structure_pass=True,witnesses_per_source_step=stride+2,squares_per_source_step=r+3,square_constant=2,products_per_source_step=b+1)
    if source is None:return out
    w=read(c['sp']/'accepting_peak_witness_N446.json');oldw=read(c['bp']/'accepting_peak_witness.json');assert w['nonzero_coordinates']==oldw['nonzero_coordinates']
    h=len(source);assert w['variable_count']==h*(stride+2);x=dict(w['nonzero_coordinates']);assert len(x)==len(w['nonzero_coordinates'])
    assert all(type(i) is int and 0<=i<w['variable_count'] and type(v) is int and v>0 for i,v in x.items())
    def coord(j,i):return x.get(j*stride+i if i<stride else h*stride+2*j+(i-stride),0)
    def affine(a,j,f):return a['constant']+sum(coef*f[name] for name,coef in a['forms'])+sum(coef*coord(j,i) for i,coef in a['variables'])+sum(coef*w['parameters'][name] for name,coef in a['parameters'])
    prevq=new['entry_code'];prevregs=[6,0,0];peak=6;Z=0;squares=products=0
    for j,srow in enumerate(source):
        f={name:sum(coef*coord(j,i) for i,coef in terms) for name,terms in new['linear_forms'].items()}
        assert f['E:0']==1 and f['Q:0']==prevq;squares+=2
        assert [f[f'OLD{i}:0'] for i in range(r)]==prevregs;squares+=r
        act=[i for i in range(b) if coord(j,i)];assert len(act)==1 and branches[act[0]]['name']==srow[0]
        regs=[f[f'NEW{i}:0'] for i in range(r)];assert regs==srow[2]
        u,v=coord(j,stride),coord(j,stride+1);assert peak+u-sum(regs)-v==0;squares+=1;peak=sum(regs)+v
        Z+=f['SOURCE_ZERO_COUNT'];prevq=f['D:0'];prevregs=regs
        for term in new['quadratic_products']:
            left=affine(term['left'],j,f);right=affine(term['right'],j,f);assert left>=0 and right>=0 and left*right==0;products+=1
    assert prevq==new['halt_code'];squares+=1
    residual=w['parameters']['N']-h-3*sum(prevregs)+6-2*coord(h-1,stride+1)-(r+2)-2*Z;assert residual==0;squares+=1
    assert (squares,products,Z)==(1970,249936,29)
    out.update(full_horizon=h,full_witness_coordinates=w['variable_count'],sparse_nonzero_coordinates=len(x),affine_squares_evaluated=squares,quadratic_products_evaluated=products,polynomial_value=0,source_zero_count=Z,duration_minus_or_plus_one_rejected=True)
    return out

def main():
    result={'status':'passed','independence':'Reads JSON and standard-library modules only; never imports or executes producer code. All outputs stay in this audit directory.','variants':{}}
    for label in ['three-counter','two-counter']:
        c,st=structure(label);print(label,'structure passed',flush=True)
        st['adversarial_local_phases']=adversarial(c);print(label,'adversarial passed',flush=True)
        if label=='three-counter':st['replay'],source=replay_three(c)
        else:source=None
        st['canonical_schema']=schema_check(c,source);result['variants'][label]=st
    result['input_sha256']=HASH
    (OUT/'audit_receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
