"""Sign-safe native norm units after paid positive graph definitions.

Ordinary strong form has a positive-zero root-coordinate bijection.
Optional strong normalization preserves the accepted outer projection
by a positive embedding and a fresh canonical five-auxiliary extension.
"""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random

import sympy as sp

import native_binary_computed_fields as fields

scale=fields.scale
execute=fields.execute



def register_leaves(value):
    """Declared interface trees may contain dictionaries, sequences or None."""
    if isinstance(value,str):return {value}
    if isinstance(value,dict):value=value.values()
    elif not isinstance(value,(list,tuple)):return set()
    result=set()
    for child in value:result.update(register_leaves(child))
    return result

def rewrite(old,prefix=None,*,normalized=False):
    assert old.get('native_computed_fields') and not old.get('native_norm_units')
    prefix=old['computed_prefix'] if prefix is None else prefix
    assert prefix==old['computed_prefix']
    audited=fields.rewrite(old['computed_parent'],old['computed_fields'],prefix)
    assert all(old[k]==audited[k] for k in ('source','comparisons','parameters','auxiliaries'))
    n=lambda v:prefix+v
    alias=lambda v:old['computed_substitutions'].get(n(v),n(v))
    rows={name:(op,a,b) for name,op,a,b in old['source']}
    consumers=lambda v:{name for name,_,a,b in old['source'] if v in (a,b)}
    deleted={n(k) for k in ('tauplus1','R9','UM2','scaled_norm_coefficient','ratio_product2','L9')}
    assert all(consumers(v)<=deleted for v in deleted)
    assert consumers(n('tau'))=={n('tauplus1'),n('R9')}
    private={n(k) for k in ('R15','P17','bs_q')}
    assert all(not consumers(v) for v in private)
    assert not consumers(n('L17'))
    assert [pair for pair in old['comparisons'] if n('L17') in pair]==[(n('L17'),n('P17'))]
    removed=[(n('L15'),n('R15')),(n('L17'),n('P17')),
             (n('L9'),n('R9')),(n('bs_q'),n('q'))]
    assert all(old['comparisons'].count(pair)==1 for pair in removed)
    assert (n('ic22'),n('R16')) in old['comparisons']
    affected=private|deleted|{n('tau')}
    assert not affected & register_leaves(old.get('public_registers',{}))
    assert not affected & register_leaves(old.get('interfaces',{}))
    assert all(pair in removed for pair in old['comparisons'] if affected & set(pair))
    change={n('R15'):('-',n('L15'),n('Ac2')),
            n('L17'):('*',n('R16'),n('aux_square_gap')),
            n('P17'):('+',n('L17'),n('aux_y2')),
            n('bs_q'):('-',n('q'),n('bs_Q'))}
    source=[(name,*change[name]) if name in change else row
            for row in old['source'] for name in [row[0]] if name not in deleted]
    source += [(n('gap_square'),'*',n('tau_gap'),n('tau_gap')),
               (n('root_base'),'*',n('UM'),n('ksn2')),
               (n('signed_gap'),'-',n('tau_gap'),alias('k')),
               (n('gap_cross'),'*',n('root_base'),n('signed_gap')),
               (n('four_cross'),'*',4,n('gap_cross')),
               (n('first_unit'),'+',n('gap_square'),n('four_cross'))]
    factors=[n('R15'),n('P17'),n('first_unit'),n('bs_q')]
    last=factors[0]
    for j,f in enumerate(factors[1:]):
        new=n('norm_unit_product'+str(j));source.append((new,'*',last,f));last=new
    aux=[n('tau_gap') if v==n('tau') else v for v in old['auxiliaries']]
    source=scale.sort_source(source,old['parameters']+aux)
    scale.checked_source(source,old['parameters'],aux)
    packet=scale.metadata(dict(old,source=source,
        comparisons=[pair for pair in old['comparisons'] if pair not in removed]+[(last,1)],
        auxiliaries=aux,native_norm_units=True,core_prefix=prefix,unit_parent=old,
        unit_product=True,unit_register=last,unit_factors=factors,
        norm_removed_comparisons=removed,root_coordinate=n('tau_gap'),
        normalized_strong=False))
    assert packet['operations']==old['operations']+3
    assert packet['multiplications']==old['multiplications']+3
    assert packet['additions_subtractions']==old['additions_subtractions']
    assert packet['equations']==old['equations']-3 and packet['witnesses']==old['witnesses']
    return normalize(packet) if normalized else packet


def normalize(old):
    assert old.get('native_norm_units') and not old['normalized_strong']
    n=lambda v:old['core_prefix']+v
    rows={name:(op,a,b) for name,op,a,b in old['source']}
    expected={'L16':('*',n('f'),n('f')),'f_square_minus_one':('-',n('L16'),1),
        'R16':('*',n('A'),n('f_square_minus_one')),'ic22':('*',n('ic2'),n('ic2')),
        'L17':('*',n('R16'),n('aux_square_gap'))}
    assert all(rows[n(k)]==v for k,v in expected.items())
    for key,want in [('i',{'ic2'}),('ic2',{'ic22'}),('ic22',set()),
                     ('f_square_minus_one',{'R16'}),('R16',{'L17'})]:
        assert {name for name,_,a,b in old['source'] if n(key) in (a,b)}=={n(c) for c in want}
    strong=(n('ic22'),n('R16'));linear=(n('H17'),n('aux_u_rhs'))
    assert old['comparisons'].count(strong)==1 and old['comparisons'].count(linear)==1
    rebuilt={n(k) for k in ('f','i','j','o','y_aux')}
    # Only intersections with rebuilt are used below. Projection commutes
    # with each union, so retain at most these five names per register.
    deps={name:({name} if name in rebuilt else set())
          for name in old['parameters']+old['auxiliaries']}
    dep=lambda v:deps[v] if isinstance(v,str) else set()
    for name,_,a,b in old['source']:deps[name]=dep(a)|dep(b)
    alias=lambda k:old['computed_substitutions'].get(n(k),n(k))
    assert all(not dep(v)&rebuilt for v in (n('q'),alias('a'),alias('c'),alias('r'),n('root_base')))
    for pair in old['comparisons'][:-1]:
        if pair not in (strong,linear):assert not (dep(pair[0])|dep(pair[1]))&rebuilt
    for factor in old['unit_factors']:
        if factor!=n('P17'):assert not dep(factor)&rebuilt
    for v in register_leaves(old.get('interfaces',{}))|register_leaves(old.get('public_registers',{})):
        assert not dep(v)&rebuilt
    Q=n('normalized_strong_Q');N=n('f_square_minus_one');unit=n('normalized_norm_units')
    changes={N:('-',n('L16'),Q),n('R16'):('*',n('A'),Q)}
    source=[(name,*changes[name]) if name in changes else row
            for row in old['source'] for name in [row[0]]]
    source += [(Q,'*',n('A'),n('ic22')),(unit,'*',old['unit_register'],N)]
    source=scale.sort_source(source,old['parameters']+old['auxiliaries'])
    scale.checked_source(source,old['parameters'],old['auxiliaries'])
    packet=scale.metadata(dict(old,source=source,
        comparisons=[p for p in old['comparisons'][:-1] if p!=strong]+[(unit,1)],
        unit_register=unit,unit_factors=old['unit_factors']+[N],normalized_strong=True,
        normalized_parent=old,normalized_strong_factor=N,removed_strong_comparison=strong,
        rebuilt_auxiliaries=sorted(rebuilt),canonical_dependency_audit=True))
    assert packet['operations']==old['operations']+2
    assert packet['equations']==old['equations']-1
    return packet


def build(context='and',*,scaled=True,computed='six',normalized=True):
    old=fields.build(context,scaled,fields.VARIANTS[computed])
    return rewrite(old,normalized=normalized)


def polynomial_source(packet,*,sum_of_squares=False):
    assert packet['comparisons'][-1]==(packet['unit_register'],1)
    if sum_of_squares:return scale.polynomial_source(packet)
    source=list(packet['source']);last=None
    for j,(a,b) in enumerate(packet['comparisons'][:-1]):
        rr='norm_residual'+str(j);ss='norm_square'+str(j)
        source += [(rr,'-',a,b),(ss,'*',rr,rr)]
        if last is None:last=ss
        else:
            name='norm_sum'+str(j);source.append((name,'+',last,ss));last=name
    assert last is not None
    source += [('norm_outer_positive','+',last,1),
        ('norm_outer_product','*',packet['unit_register'],'norm_outer_positive'),
        ('norm_output','-','norm_outer_product',1)]
    assert len(source)==packet['operations']+3*packet['equations']-1
    return source,'norm_output'


def lift_to_parent(packet,values):
    """To ordinary-unit parent if normalized, else to computed-field parent.

    The ordinary-unit root lift can be half-integral off the norm zeros.
    """
    env=execute(packet['source'],values);p=packet['core_prefix']
    if packet['normalized_strong']:
        return dict(values,**{p+'i':env[p+'A']*values[p+'i']})
    old={name:values[name] for name in packet['unit_parent']['parameters']+
         packet['unit_parent']['auxiliaries'] if name in values}
    old[p+'tau']=env[p+'root_base']+Fraction(values[p+'tau_gap']-1,2)
    return old


def project_from_parent(packet,values):
    assert not packet['normalized_strong'],'Normalization uses fresh canonical auxiliaries, not erasure.'
    old=packet['unit_parent'];env=execute(old['source'],values);p=packet['core_prefix']
    result={name:values[name] for name in packet['parameters']+packet['auxiliaries'] if name in values}
    result[p+'tau_gap']=2*values[p+'tau']+1-2*env[p+'UM']*env[p+'ksn2']
    return result


def degree_bound(packet,*,sum_of_squares=False):
    degrees={n:1 for n in packet['parameters']+packet['auxiliaries']}
    d=lambda v:degrees[v] if isinstance(v,str) else 0
    rows={n:(op,a,b) for n,op,a,b in packet['source']};p=packet['core_prefix']
    for n,op,a,b in packet['source']:
        degrees[n]=d(a)+d(b) if op=='*' else max(d(a),d(b))
        # This exact source identity, rather than any zero equation, cancels
        # the a^2*c^2 term whenever d is one of the paid computed fields.
        if n==p+'R15' and 'd' in packet['computed_fields']:
            alias=lambda k:packet['computed_substitutions'].get(p+k,p+k)
            aa,cc=alias('a'),alias('c');X,G=p+'wn2',p+'gam'
            expected={p+'R15':('-',p+'L15',p+'Ac2'),p+'L15':('*',p+'R14',p+'R14'),
                p+'R14':('+',p+'D1',G),p+'D1':('+',X,p+'cam2'),
                p+'cam2':('*',cc,aa),p+'A':('+',p+'a_square',p+'a4m5'),
                p+'a_square':('*',aa,aa),p+'a4m5':('+',p+'a4',3),p+'a4':('*',4,aa),
                p+'gam':('*',p+'ga',p+'a4m5'),p+'Ac2':('*',p+'A',p+'c2'),p+'c2':('*',cc,cc)}
            assert all(rows[k]==v for k,v in expected.items())
            degrees[n]=max(2*d(X),d(X)+d(aa)+d(cc),d(X)+d(G),
                d(aa)+d(cc)+d(G),2*d(G),d(p+'a4m5')+2*d(cc))
    residual=max(max(d(a),d(b)) for a,b in packet['comparisons'][:-1])
    unit=d(packet['unit_register'])
    return dict(degree_upper_bound=2*max(unit,residual) if sum_of_squares else unit+2*residual,
                factor_degree_bounds=[d(f) for f in packet['unit_factors']],
                unit_degree_bound=unit,maximum_residual_degree_bound=residual,
                exact_degree_claimed=False)


def ledger(packet):
    records={}
    for sos in (False,True):
        source,out=polynomial_source(packet,sum_of_squares=sos);c=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
        records['SOS' if sos else 'product']=dict(operations=len(source),multiplications=c['M'],
            additions_subtractions=c['A'],output=out,**degree_bound(packet,sum_of_squares=sos))
    return dict(certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},**records)


def audit(packet,cases=64,seed=836915):
    rng=random.Random(seed);p=packet['core_prefix'];n=lambda k:p+k
    source,out=polynomial_source(packet);sos,sosout=polynomial_source(packet,sum_of_squares=True)
    old=packet['normalized_parent'] if packet['normalized_strong'] else packet['unit_parent']
    scalar=lambda e,v:e[v] if isinstance(v,str) else v
    even=0
    for j in range(cases):
        positive=j<cases//2
        draw=lambda:rng.randrange(1,7) if positive else rng.randrange(-4,5)
        values={k:draw() for k in packet['parameters']+packet['auxiliaries']}
        if positive:values[n('tau_gap')]=2*(1+j%3) if j%2 else 2*(1+j%3)+1
        env=execute(source,values);restored=lift_to_parent(packet,values);before=execute(old['source'],restored)
        if packet['normalized_strong']:
            Delta,N=env[n('A')],env[n('f_square_minus_one')]
            rr=before[n('ic22')]-before[n('R16')]
            assert rr==Delta*(1-N)
            fs=[before[f] if f!=n('P17') else before[f]+rr*env[n('aux_square_gap')] for f in old['unit_factors']]+[N]
            remaining=[(a,b) for a,b in old['comparisons'][:-1] if (a,b)!=packet['removed_strong_comparison']]
        else:
            rr={(a,b):scalar(before,a)-scalar(before,b) for a,b in old['comparisons']}
            fs=[1+rr[(n('L15'),n('R15'))],
                1+rr[(n('L17'),n('P17'))]-rr[(n('ic22'),n('R16'))]*before[n('aux_square_gap')],
                1-4*rr[(n('L9'),n('R9'))],1-rr[(n('bs_q'),n('q'))]]
            remaining=[pair for pair in old['comparisons'] if pair not in packet['norm_removed_comparisons']]
            assert project_from_parent(packet,restored)==values
            if positive and values[n('tau_gap')]%2==0:
                assert restored[n('tau')].denominator==2;even+=1
        assert fs==[env[f] for f in packet['unit_factors']]
        rs=[scalar(before,a)-scalar(before,b) for a,b in remaining]
        assert rs==[scalar(env,a)-scalar(env,b) for a,b in packet['comparisons'][:-1]]
        product=1
        for f in fs:product*=f
        assert env[out]==product*(1+sum(r*r for r in rs))-1
        assert execute(sos,values)[sosout]==(product-1)**2+sum(r*r for r in rs)
        if positive:assert min(restored.values())>0
    return dict(complete_factor_residual_both_output_identities=cases,signed_cases=cases//2,
                positive_lifts=cases//2,half_integral_offzero_root_lifts=even)



def pell(A,index):
    """Binary exponentiation in Z[sqrt(A^2-1)], for canonical fixtures."""
    D=A*A-1;x,y=1,0;u,v=A,1
    while index:
        if index&1:x,y=x*u+D*y*v,x*v+y*u
        u,v=u*u+D*v*v,2*u*v;index//=2
    return x,y


def canonical_audit():
    records=[]
    for A in range(3,11):
        J=3;D=A*A-1;C,c=pell(A,J);m=2*c*J;f,t=pell(A,m)
        assert t%c**2==0
        i=t//c**2;T=D*t;ch,y=pell(T,J)
        assert ch%T==0
        U=ch//T
        assert (U+J)%c==0 and (U+c)%f==0
        j,o=(U+J)//c,(U+c)//f
        assert min(i,j,o,y,f)>0
        assert f*f-D*(i*c*c)**2==1
        assert T*T*(U*U-y*y)+y*y==1 and U==j*c-J==o*f-c
        records.append(dict(A=A,J=J,c=c,m=m,largest_witness_bits=max(v.bit_length() for v in (f,i,j,o,y))))
    roots=0
    for V in range(1,17):
      for n in range(1,9):
        root,k=pell(2*V+1,n);tau=(root-1)//2
        assert root%2==1 and tau*(tau+1)==V*(V+1)*k*k
        g=2*tau+1-2*V*k
        assert g>0 and g%2==1 and g*g+4*V*k*(g-k)==1
        assert V*k+(g-1)//2==tau
        roots+=1
    return dict(fresh_five_auxiliary_cases=records,positive_first_root_bijections=roots,
                scope='Small exact native norm extensions and first-root solutions, not complete AND/host Pell zeros.')


def slice_audit(packet):
    t=sp.Symbol('t');values={name:sp.Poly((1+j%5)*t+j+1,t)
        for j,name in enumerate(packet['parameters']+packet['auxiliaries'])}
    # Do not expand the group product: its degree is the sum of the exact
    # factor degrees, and the squared-residual top coefficients add positively.
    product_names={n for n,_,_,_ in packet['source'] if n.startswith(packet['core_prefix']+'norm_unit_product')}
    if packet['normalized_strong']:product_names.add(packet['unit_register'])
    source=[row for row in packet['source'] if row[0] not in product_names]
    env=execute(source,values);at=lambda v:env[v] if isinstance(v,str) else sp.Poly(v,t)
    fs=[at(f) for f in packet['unit_factors']]
    rr=[at(a)-at(b) for a,b in packet['comparisons'][:-1]]
    ud=sum(f.degree() for f in fs);rd=max(r.degree() for r in rr)
    assert all(not f.is_zero for f in fs)
    answer=dict(factor_slice_degrees=[int(f.degree()) for f in fs],
                residual_slice_maximum=int(rd),product_degree_lower_bound=int(ud+2*rd),
                SOS_degree_lower_bound=int(2*max(ud,rd)))
    assert answer['product_degree_lower_bound']<=degree_bound(packet)['degree_upper_bound']
    assert answer['SOS_degree_lower_bound']<=degree_bound(packet,sum_of_squares=True)['degree_upper_bound']
    return answer


def nested_export_audit():
    base=fields.build()
    good=dict(base,interfaces={'nested':[None,{'port':('P','F0')}]})
    normalize(rewrite(good))
    rejected=0
    for tree in ({'nested':[None,{'port':('R15',)}]},
                 {'nested':({'port':['tau']},None)}):
        try:rewrite(dict(base,interfaces=tree))
        except AssertionError:rejected+=1
        else:raise AssertionError('nested private export accepted')
    for key in ('interfaces','public_registers'):
        ordinary=rewrite(dict(base,**{key:{'nested':[None,{'port':('f',)}]}}))
        try:normalize(ordinary)
        except AssertionError:rejected+=1
        else:raise AssertionError('nested canonical-auxiliary export accepted')
    assert rejected==4
    return dict(accepted_nested_interface=1,rejected_nested_private_or_rebuilt_exports=rejected)

def verify():
    examples=[]
    for context in ('and','motion','toggle'):
      for scaled in (False,True):
       for computed in ('four','six'):
        for normalized in (False,True):
            p=build(context,scaled=scaled,computed=computed,normalized=normalized)
            source,out=polynomial_source(p)
            examples.append(dict(context=context,scaled=scaled,computed=computed,normalized=normalized,
                ledger=ledger(p),audit=audit(p,64,836915+len(examples)),
                standalone_degree_slice=slice_audit(p) if context=='and' else None,
                parameters=p['parameters'],auxiliaries=p['auxiliaries'],source=source,
                comparisons=p['comparisons'],output=out,
                source_sha256=hashlib.sha256(json.dumps(source,sort_keys=True).encode()).hexdigest()))
    signs=0
    for a in range(4):
     for c in range(4):
      for d in range(4):
       for f in range(4):
        D=a*a+4*a+3;K=D*(f*f-1)
        assert (d*d-D*c*c)%4!=3 and (f*f-D*c*c)%4!=3
        for u in range(4):
         for y in range(4):
          assert (K*(u*u-y*y)+y*y)%4!=3
          assert ((D*c)**2*(u*u-y*y)+y*y)%4!=3
          signs+=1
    assert ledger(build())['product']['operations']==83
    return dict(status='PASS_NATIVE_BINARY_NORM_UNITS',examples=examples,
        complete_factor_residual_both_output_identities=64*len(examples),signed_cases=32*len(examples),
        residue_sign_cases=signs,canonical_and_root_audit=canonical_audit(),nested_export_audit=nested_export_audit(),scope='Ordinary units preserve full positive zeros through a root-gap bijection; '
            'strong normalization preserves all coordinates except five rebuilt native auxiliaries. '
            'All arithmetic gates remain paid; both integer finalizers are complete. Components only, '
            'no program-control/input universal bound and no full numeric Pell-zero fixtures.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
    for r in result['examples']:
        if r['scaled'] and r['computed']=='six':print(r['context'],r['normalized'],r['ledger'])
