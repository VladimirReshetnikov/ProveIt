#!/usr/bin/env python3
"""Independent full-row/prefix/call checker for the21 omitted guard signs.

No producer, Pell emitter, proof compiler, or concrete source exponentiation is
executed. Universal order/induction arguments are the ordinary proof in README;
this checker binds every finite source interface and verifies its ideal identities.
"""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys
import zipfile

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
REPO=ROOT.parents[1]
BASE=ROOT/'candidates/projected-radius-mixed-bounds'


def need(ok,text):
    if not ok:raise ValueError(text)


def load(p):return json.loads(p.read_text())
def digest(data):return sha256(data).hexdigest()
def canonical(v):return json.dumps(v,sort_keys=True,separators=(',',':'))


def poly(terms):
    out={}
    for c,m in terms:
        need(type(c)is int and isinstance(m,list)and all(type(i)is int and i>=0 for i in m),'literal integer polynomial')
        k=tuple(sorted(m));out[k]=out.get(k,0)+c
    return{m:c for m,c in out.items()if c}


def add(p,q,scale=1):
    out=dict(p)
    for m,c in q.items():out[m]=out.get(m,0)+scale*c
    return{m:c for m,c in out.items()if c}


def mul(p,q):
    out={}
    for m,c in p.items():
        for n,d in q.items():
            k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
    return{m:c for m,c in out.items()if c}


def atom(v):return{(v,):1}
def const(c):return{():c}if c else{}
def plus(*ps):
    p={}
    for q in ps:p=add(p,q)
    return p


def times(*ps):
    p=const(1)
    for q in ps:p=mul(p,q)
    return p


def power(p,k):
    need(type(k)is int and k>=0,'literal finite polynomial power')
    q=const(1)
    for _ in range(k):q=mul(q,p)
    return q


def nonnegative(p,known,strict=False):
    shifted={}
    for m,c in p.items():
        term=const(c)
        for v in m:term=mul(term,plus(atom(v),const(known.get(v,0))))
        shifted=add(shifted,term)
    need(all(c>0 for c in shifted.values()),'nonnegative shifted polynomial coefficients')
    need(all(m.count(v)%2==0 or v in known for m in shifted for v in set(m)),'all shifted odd-coordinate signs supplied')
    if strict:need(shifted.get((),0)>0,'strict shifted constant')
    return shifted


def ideal(raw,comb):
    out={}
    need(bool(comb),'nonempty actual-row combination')
    for item in comb:
        i=item['row'];need(type(i)is int and 0<=i<len(raw['rows']),'actual original-row index')
        p=poly(item['multiplier']);need(all(i<len(raw['variables'])for m in p for i in m),'ideal multiplier indices')
        out=add(out,mul(p,poly(raw['rows'][i]['terms'])))
    return out


def cut(raw,item,expected,label):
    need(poly(item['polynomial'])==expected and ideal(raw,item['row_combination'])==expected,
         'entire expanded original-row cut: '+label)


def bound(raw,s,known,prefix=False):
    v,L=s['variable'],s['lower'];F,G=poly(s['factor']),poly(s['rhs'])
    need(type(v)is int and 0<=v<1259 and v not in known and type(L)is int and L>=0,'fresh integer lower-bound target')
    need(all(0<=i<1259 and i!=v for p in[F,G]for m in p for i in m),'bound factor/RHS independent of target')
    if prefix:
        need(v<643 and all(i<643 for p in[F,G]for m in p for i in m),'prefix-only target/factor/RHS')
        need(all(x['row']<594 and all(i<643 for m in poly(x['multiplier'])for i in m)for x in s['row_combination']),
             'prefix-only bound rows and multipliers')
    need(ideal(raw,s['row_combination'])==add(mul(atom(v),F),G,-1),'complete integer lower-bound ideal')
    nonnegative(F,known,True);nonnegative(add(G,F,-(L-1)),known,True)
    known[v]=L
    return dict(variable=v,lower=L,original_rows=len(s['row_combination']))


def sign(raw,s,known,prefix=False):
    v,c,r=s['variable'],s['coefficient'],s['row'];rhs=poly(s['rhs'])
    need(type(c)is int and c>0 and type(v)is int and 0<=v<1259 and v not in known,'fresh sign pivot')
    need(type(r)is int and 0<=r<1177 and all(i<1259 and i!=v for m in rhs for i in m),'sign row/operand bounds')
    expected=add({(v,):c},rhs,-1);actual=poly(raw['rows'][r]['terms'])
    need(actual in[expected,{m:-a for m,a in expected.items()}],'entire actual sign-row identity')
    if s['kind']=='affine_square':
        root=poly(s['square_root'])
        need(all(len(m)<=1 for m in root)and mul(root,root)==rhs,'entire affine-square identity')
        deps=set()
    else:
        need(s['kind']=='positive_monomials'and all(d>0 for d in rhs.values()),'nonnegative RHS coefficients')
        deps={i for m in rhs for i,n in Counter(m).items()if n%2}
    need(s['dependencies']==sorted(deps)and deps<=set(known),'all actual odd-power sign dependencies')
    if prefix:
        need(v<643 and r<594 and all(i<643 for m in rhs for i in m),'prefix-only sign inference')
        need(s['kind']!='affine_square'or all(i<643 for m in root for i in m),'prefix-only affine-square root')
    known[v]=0


def verify(raw,body,old,interfaces,cert):
    need(len(raw['variables'])==1259 and len(raw['rows'])==1177,'whole raw1259/1177 source')
    ids={canonical(v):i for i,v in enumerate(raw['variables'])}
    need(len(ids)==1259,'distinct complete variable metadata')
    retained=[ids[canonical(v)]for v in body['variables']]
    need(retained==load(BASE/'source/raw_restoration.json')['retained_raw_indices']and len(retained)==667,'full actual raw/contracted correspondence')
    previous=[g['raw_variable']for g in old['guards']]
    Xs=[s['pair'][0][1]for s in raw['seeds']]
    Tdata=[(5,694,644),(92,730,677),(103,742,689),(87,753,700),(112,764,711),(531,798,743),(530,810,755)]
    removed=set(Xs)|{T for n,T,rid in Tdata if T!=694}
    need(len(previous)==100 and cert['original_guard_indices']==previous,'complete existing100-guard boundary')
    need(cert['removed_guard_identities']==[dict(raw_variable=i,contracted_variable=retained.index(i),metadata=raw['variables'][i])for i in sorted(removed)]
         and len(removed)==21,'exact15 X and6 noninitial T identities')
    remaining=[i for i in previous if i not in removed]
    need(cert['remaining_raw_guard_indices']==remaining and len(remaining)==79,'exact79 retained guards')
    expected_private={694,657,1214}|{s['YminusK'][1]for s in interfaces['seeds']}
    semantic=[i for i in previous if i<643]
    need(len(semantic)==61 and set(remaining)==set(semantic)|expected_private,'complete retained semantic/private partition')
    p=cert['prefix_proof'];need(p['initial_semantic_guard_indices']==semantic,'only61 prefix guards used')
    known={i:0 for i in semantic}
    need(p['preliminary_t_n_bounds']==load(BASE/'source/four_bounds.json')[:2],'literal initial t/n bound certificates')
    results=[bound(raw,s,known,True)for s in p['preliminary_t_n_bounds']]
    need([(r['variable'],r['lower'])for r in results]==[(4,1),(5,2)],'initial strict t/n bounds')
    stages=p['five_stages'];need([(s['variable'],s['lower'])for s in stages]==[(87,0),(107,0),(130,0),(517,0),(32,1)],'five acyclic prefix stages')
    counts=[]
    for s in stages:
        for step in s['preceding_sign_steps']:sign(raw,step,known,True)
        if s['variable']==517:need(516 in known,'actual CRT numerator nonnegative before quotient')
        results.append(bound(raw,s,known,True));counts.append(len(s['preceding_sign_steps']))
    need([s['row']for s in p['final_sign_steps']]==[36,37],'two actual endpoint constructors')
    for s in p['final_sign_steps']:sign(raw,s,known,True)
    need(p['required_nonnegative_coordinates']==list(range(643))and set(known)==set(range(643)),
         'every semantic-prefix sign proved without private coordinates')
    positive=cert['positive_prefix']
    M=plus(const(1),times(atom(87),plus(const(1),atom(59))))
    cut(raw,positive['canonical_modulus_cut'],add(M,atom(129),-1),'canonical positive modulus')
    nonnegative(M,known,True)
    need(positive['initial_positive_coordinates']==[4,5,129],'three independently positive initial coordinates')
    strict={4,5,129}
    for s in positive['steps']:
        v,r=s['variable'],s['row'];need(v in known and v not in strict and r<594,'fresh prefix positivity constructor')
        row=raw['rows'][r];q=poly(row['terms'])
        need(row.get('gate')==v and q.get((v,))==1 and all(v not in m or m==(v,)for m in q),'actual monic prefix constructor')
        rhs={m:-c for m,c in q.items()if m!=(v,)}
        witness=tuple(sorted(s['positive_monomial']))
        need(all(c>0 and all(i<643 for i in m)for m,c in rhs.items())and witness in rhs and set(witness)<=strict,
             'strictly positive actual monomial with already positive factors')
        strict.add(v)
    ks=[s['exponent'][1]for s in raw['seeds']]
    need(ks==[4,86,90,110,122,44,46,48,50,52,36,54,56,136,58]
         and positive['required_seed_exponents']==ks and set(ks)<=strict,'every literal exponent is at least1; no k0 case')
    need(positive['known_after']==sorted(strict),'entire strict-positive constructor ledger')
    need(positive['independent_positive_bases']==[5,92,103,112,531,530]
         and set(positive['independent_positive_bases'])<=strict,'all six positive bases independent of f0 strictness')
    # Only retained T0 is now allowed to enter the carrier bound.
    known[694]=0
    need(cert['initial_A_D_bounds']==load(BASE/'source/four_bounds.json')[2:],'actual A/D lower bounds')
    ad=[bound(raw,s,known)for s in cert['initial_A_D_bounds']]
    need([(r['variable'],r['lower'])for r in ad]==[(644,2),(917,2)],'A>=2 and D>=2 before omitted guard signs')
    arguments=sorted({p[k][1]for p in raw['powers']for k in['base','exponent','output']})
    need(cert['frame_arguments']==arguments and all(i<643 for i in arguments),'all actual21-call arguments in natural prefix')
    cut(raw,cert['frame_cut'],plus(atom(643),const(-2),*[{(i,):-1}for i in arguments]),'W=2+sum distinct actual arguments')
    A,W,Z,U,V,B=map(atom,[644,643,646,655,656,667])
    boot=cert['bootstrap_norm']
    expected=plus(power(A,2),const(-1),times(const(-1),power(W,3),plus(W,const(2)),power(Z,2)))
    need(boot['factorized_symbols']==dict(A=644,W=643,Z=646,Zminus1=645)and boot['affine_Z_definition_row']==594,'literal bootstrap factor roles')
    need(poly(boot['expanded_polynomial'])==expected and ideal(raw,boot['row_combination'])==expected,'complete9-row bootstrap norm ideal')
    need(poly(raw['rows'][594]['terms'])==plus(Z,{(645,):-1},const(-1)),'actual affine Z=1+z0 constructor')
    cut(raw,cert['unit_norm_cut'],plus(power(U,2),times(const(-1),add(power(A,2),const(1),-1),power(V,2)),const(-1)),'unit norm')
    cut(raw,cert['comparison_base_constructor'],plus(B,const(-1),times(const(-4),V,plus(atom(657),const(1)))),'positive comparison B')
    cut(raw,cert['comparison_base_congruence'],plus(B,{(644,):-1},times(const(-1),U,atom(658))),'B congruent A modulo U')
    Ys=[s['pair'][1][1]for s in raw['seeds']]
    cut(raw,cert['positive_V_product'],add(V,times(*[power(atom(y),2)for y in Ys],plus(atom(1214),const(1))),-1),'all15 Y-square factors and retained V slack')
    need(len(cert['moduli'])==7,'all seven actual modulus interfaces')
    moduli={}
    for s,(n,T,r)in zip(cert['moduli'],Tdata):
        need((s['base'],s['modulus'],s['row'])==(n,T,r)and s['early_positive_base']==(n!=87)and s['retained_guard']==(T==694),'exact modulus/dependency schedule')
        cut(raw,s['cut'],plus(times(const(2),A,atom(n)),{(T,):-1},times(const(-1),power(atom(n),2)),const(-1)),'modulus '+str(T))
        moduli[n]=T
    pairs={tuple(x['exponent']):x['pair']for x in raw['indices']}
    need(len(cert['power_calls'])==len(raw['powers'])==len(interfaces['powers'])==21,'all21 actual power calls')
    for j,(s,p,i)in enumerate(zip(cert['power_calls'],raw['powers'],interfaces['powers'])):
        need(all(p[k]==i[k]for k in['base','exponent','output']),'independently supplied call metadata agrees')
        n,k,m=[p[v][1]for v in['base','exponent','output']];X,Y=[v[1]for v in pairs[tuple(p['exponent'])]]
        expected_meta=dict(index=j,base=n,exponent=k,output=m,X=X,Y=Y,quotient=i['quotient'][1],modulus=moduli[n],row=i['row'])
        need(all(s[key]==v for key,v in expected_meta.items())and s['semantic_value_used_before_all_guard_recovery']==(j==1),'whole actual call/pair/quotient/row binding and semantic schedule')
        cut(raw,s['cut'],plus(atom(X),times(atom(n),atom(Y)),times(const(-1),A,atom(Y)),{(m,):-1},times(const(-1),atom(s['modulus']),atom(s['quotient']))),'actual power call '+str(j))
    need(len(cert['seeds'])==len(raw['seeds'])==len(interfaces['seeds'])==15,'all15 actual signed-index instances')
    selected=[]
    for j,(s,p,i)in enumerate(zip(cert['seeds'],raw['seeds'],interfaces['seeds'])):
        keys=['X','Y','S','R','exponent','YminusK','Squotient','Rquotient']
        aliases={('k'if key=='exponent'else key):i[key][1]for key in keys}
        need(p['exponent']==i['exponent']and p['pair']==[i['X'],i['Y']]and s['aliases']==aliases and s['rows']==i['rows'],'full literal seed aliases and row indices')
        need(s['exponent_strictly_positive']and aliases['k']in strict and aliases['YminusK']in remaining,'positive index and actual retained YminusK')
        X,Y,S,R,k,d,sq,rq=[atom(aliases[key])for key in['X','Y','S','R','k','YminusK','Squotient','Rquotient']]
        expected_cuts=dict(index_at_most_Y=plus(Y, times(const(-1),k),times(const(-1),d)),
            norm1=plus(power(X,2),times(const(-1),add(power(A,2),const(1),-1),power(Y,2)),const(-1)),
            norm3=plus(power(S,2),times(const(-1),add(power(B,2),const(1),-1),power(R,2)),const(-1)),
            S_mod_U=plus(S,times(const(-1),X),times(const(-1),U,sq)),
            R_mod_4Y=plus(R,times(const(-1),k),times(const(-4),Y,rq)))
        need(set(s['cuts'])==set(expected_cuts),'complete five signed-index conditions')
        for name,e in expected_cuts.items():cut(raw,s['cuts'][name],e,'seed '+str(j)+' '+name)
        call=s['selected_power_call'];need(type(call)is int and 0<=call<21,'selected actual supporting call')
        c=cert['power_calls'][call]
        need(c['exponent']==aliases['k']and c['X']==aliases['X']and c['Y']==aliases['Y']
             and c['base']in[5,92,531,530]and c['base']in strict and c['modulus']!=753,
             'same seed/exponent has an independent positive-base supporting call')
        selected.append(call)
    need(len(set(selected))==15,'distinct selected calls cover all15 oriented roots')
    early=cert['power_calls'][cert['early_exact_value_call']]
    need(cert['early_exact_value_call']==1 and [early[k]for k in['base','exponent','output','X','Y','modulus']]==[92,86,93,707,708,730],
         'only actual pow1 interpreted before final T recovery, never a raw87 call')
    first=stages[0]
    need(first['variable']==87 and poly(first['factor'])==plus(const(1),atom(94),atom(95))
         and poly(first['rhs'])==plus(atom(93),atom(95)),
         'exact f0*(r0+s0+1)=V0+s0 identity uses newly positive pow1 output93')
    target=cert['pointwise_map']
    need(target==dict(body_values_changed=0,existing_guard_triples_copied=79,fresh_guard_triples=21,fresh_integer_witnesses=63,
         missing_target_guard_records=[g for g in old['guards']if g['raw_variable']in removed]),'exact pointwise extension into frozen967 guard slots')
    return dict(retained_guards=79,omitted_guards=21,semantic_prefix_coordinates=643,
        prefix_initial_guards=61,prefix_sign_rows=sum(counts)+2,prefix_stage_sign_rows=counts,
        prefix_lower_bounds=results,carrier_lower_bounds=ad,strict_positive_constructor_rows=len(positive['steps']),
        strict_positive_actual_exponents=ks,distinct_frame_arguments=len(arguments),
        complete_power_calls=21,signed_index_instances=15,selected_supporting_calls=selected,
        modulus_dependency_order=[694,730,742,764,798,810,753],
        body_values_changed=0,fresh_integer_guard_witnesses=63)


def universal_algebra():
    # Small formal polynomial variables, unrelated to actual giant source values.
    A,n,x,y,m,p,q,r,T,W,Z=map(atom,range(11))
    D=add(power(A,2),const(1),-1);a=add(A,n,-1)
    t=plus(times(const(2),A,n),times(const(-1),power(n,2)),const(-1))
    P=add(x,mul(a,y),-1);Q=add(x,mul(a,y))
    norm=plus(power(x,2),times(const(-1),D,power(y,2)),const(-1))
    identities={
        'Pell residue recurrence':plus(times(A,x),times(D,y),times(const(-1),a,plus(x,times(A,y))),times(const(-1),n,P),times(const(-1),t,y)),
        'Pell product from norm':plus(times(P,Q),const(-1),times(const(-1),t,power(y,2)),times(const(-1),norm)),
        'negative-root inverse residue':plus(times(m,r),const(1),times(m,add(p,r,-1)),times(const(-1),p,plus(m,q)),add(times(p,q),const(1),-1)),
        'T minus A positive decomposition':plus(t,times(const(-1),A),times(const(-1),add(times(const(2),n),const(1),-1),add(add(A,n,-1),const(1),-1)),times(const(-1),add(n,const(1),-1),plus(n,const(2)))),
        'bootstrap square gap':plus(power(A,2),times(const(-1),power(W,4)),times(const(-1),plus(const(1),times(const(2),power(W,3)),times(power(W,3),plus(W,const(2)),add(power(Z,2),const(1),-1))))),
        'Pell descent norm preservation':add(plus(power(add(times(A,x),times(D,y),-1),2),times(const(-1),D,power(add(times(A,y),x,-1),2))),add(power(x,2),times(D,power(y,2)),-1),-1),
        'Pell descent inverse x':add(plus(times(A,add(times(A,x),times(D,y),-1)),times(D,add(times(A,y),x,-1))),x,-1),
        'Pell descent inverse y':add(plus(add(times(A,x),times(D,y),-1),times(A,add(times(A,y),x,-1))),y,-1),
    }
    # The square-gap identity holds modulo exactly the displayed bootstrap norm.
    bootstrap=plus(power(A,2),const(-1),times(const(-1),power(W,3),plus(W,const(2)),power(Z,2)))
    identities['bootstrap square gap']=add(identities['bootstrap square gap'],bootstrap,-1)
    for name,p in identities.items():need(not p,'universal collected identity: '+name)
    return sorted(identities)


def finite_controls():
    count=0
    for A in range(2,9):
        for n in range(1,min(A,7)):
            T=2*A*n-n*n-1;x,y=1,0
            for k in range(1,9):
                x,y=A*x+(A*A-1)*y,x+A*y
                p=x-(A-n)*y;q=x+(A-n)*y
                need((p-pow(n,k))%T==0 and p*q==1+T*y*y,'small exact Pell residue control')
                count+=1
    bounds=0
    for W in range(2,15):
        need((W-1)**W+1<=W**W,'small carrier endpoint control')
        for n in range(1,W):
            A=W*W+1;T=2*A*n-n*n-1
            need(T>=A,'small positive modulus control');bounds+=1
    need(-3-(3-2)*1-3==7*(-1)and 3*2+1==7,'negative-root local counterexample without strong carrier bound')
    return dict(pell_residue_controls=count,positive_modulus_controls=bounds,carrier_endpoints=13,
        counterexample_without_carrier=dict(A=3,n=2,k=1,T=7,X=-3,Y=1,m=3,h=-1),
        scope='Finite controls only; universal inequalities, induction, Pell descent and signed-index use are the ordinary proof, not sampling conclusions.')


def authenticate():
    pins=load(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(digest((ROOT/n).read_bytes())==h,'entire frozen input '+n)
    for directory in['candidates/projected-radius-mixed-bounds','candidates/projected-radius-mixed-orbits',
                     'research/guard-seed-consequences','research/guard-sign-orbits']:
        base=ROOT/directory;manifest=load(base/'MANIFEST.json')['files']
        actual={str(p.relative_to(base))for p in base.rglob('*')if p.is_file()and p.name!='MANIFEST.json'}
        need(actual==set(manifest),'closed frozen packet '+directory)
        for n,h in manifest.items():need(digest((base/n).read_bytes())==h,'whole frozen member '+directory+'/'+n)
    archive=REPO/pins['signed_index_archive']['repository_path']
    need(digest(archive.read_bytes())==pins['signed_index_archive']['sha256'],'whole signed-index archive')
    with zipfile.ZipFile(archive)as z:data=z.read(pins['signed_index_member']['path'])
    need(digest(data)==pins['signed_index_member']['sha256']and data==(HERE/'SIGNED_INDEX_THEOREM_SOURCE.md').read_bytes(),'exact reviewed signed-index source member')
    return dict(frozen_file_pins=len(pins['files']),closed_frozen_packets=4,signed_index_member_sha256=digest(data))


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);args=ap.parse_args()
    manifest=HERE/'MANIFEST.json'
    if manifest.exists():
        members=load(manifest)['files']
        need({str(p.relative_to(HERE))for p in HERE.rglob('*')if p.is_file()and p!=manifest}==set(members),'closed current research packet')
        for n,h in members.items():need(digest((HERE/n).read_bytes())==h,'sealed research member '+n)
    auth=authenticate();raw=load(BASE/'source/raw_builder.json');body=load(BASE/'source/natural667.json')
    old=load(ROOT/'candidates/projected-radius-mixed-orbits/domain_certificate.json')
    interfaces=load(ROOT/'candidates/projected-radius-mixed/arithmetic_interfaces.json');cert=load(HERE/'CERTIFICATE.json')
    result=verify(raw,body,old,interfaces,cert);mutations=[]
    def reject(label,bad):
        try:verify(raw,body,old,interfaces,bad)
        except(ValueError,RuntimeError,KeyError,IndexError,TypeError):mutations.append(label)
        else:raise ValueError('bad certificate accepted '+label)
    bad=deepcopy(cert);bad['remaining_raw_guard_indices'].append(670);reject('assumed removed X sign',bad)
    bad=deepcopy(cert);bad['remaining_raw_guard_indices'].remove(694);reject('omitted independent T0 guard',bad)
    bad=deepcopy(cert);bad['prefix_proof']['five_stages'][0]['preceding_sign_steps'][0]['dependencies'].append(670);reject('private sign smuggled into semantic prefix',bad)
    bad=deepcopy(cert);bad['prefix_proof']['five_stages'][0]['row_combination'][0]['multiplier'][0][0]+=1;reject('changed factorial full-row ideal',bad)
    bad=deepcopy(cert);bad['positive_prefix']['steps'][0]['positive_monomial']=[670];reject('unproved positive constructor factor',bad)
    bad=deepcopy(cert);bad['positive_prefix']['required_seed_exponents'][0]=0;reject('zero exponent substituted for actual positive index',bad)
    bad=deepcopy(cert);bad['bootstrap_norm']['row_combination'][0]['multiplier'][0][0]+=1;reject('changed bootstrap norm cut',bad)
    bad=deepcopy(cert);bad['moduli'][1]['early_positive_base']=False;reject('changed modulus dependency schedule',bad)
    bad=deepcopy(cert);bad['comparison_base_congruence']['polynomial'][0][0]+=1;reject('changed actual comparison congruence',bad)
    bad=deepcopy(cert);bad['seeds'][0]['aliases']['YminusK']+=1;reject('wrong retained YminusK binding',bad)
    bad=deepcopy(cert);bad['seeds'][0]['selected_power_call']=1;reject('supporting call uses a different seed exponent',bad)
    bad=deepcopy(cert);bad['seeds'].pop();reject('missing signed-index instance',bad)
    bad=deepcopy(cert);bad['power_calls'][1]['cut']['row_combination'][0]['multiplier'][0][0]+=1;reject('changed literal pow1 residue row',bad)
    bad=deepcopy(cert);bad['early_exact_value_call']=3;reject('premature exact power value at base f0',bad)
    bad=deepcopy(cert);bad['pointwise_map']['body_values_changed']=1;reject('claimed pointwise proof changed body value',bad)
    result.update(status='PASS',optimized_python=bool(sys.flags.optimize),authentication=auth,
        rejected_corruptions=mutations,universal_collected_identities=universal_algebra(),finite_controls=finite_controls(),
        certificate_sha256=digest((HERE/'CERTIFICATE.json').read_bytes()),
        ordinary_proof_sha256=digest((HERE/'README.md').read_bytes()),
        scope='Complete finite binding of original-row ideals, independent semantic-prefix/positive-constructor dependencies, all15 signed-index instances and all21 real power calls. The accompanying ordinary proof supplies universal inequalities/induction/classification and the pinned signed-index theorem. No full new quartic or improved projected count is claimed.')
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')


if __name__=='__main__':main()
