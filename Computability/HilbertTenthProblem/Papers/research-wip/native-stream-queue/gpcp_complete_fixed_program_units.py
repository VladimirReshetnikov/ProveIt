"""Positive native-unit projections for the complete fixed-program compiler.

Regroup nine independently sign-safe norms with ONE unrestricted checksum.
The second checksum remains an explicit comparison.  Two arbitrary checksum
units must never be silently merged into the same sign argument.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import gpcp_complete_fixed_program as parent
import native_binary_input_dilation_unit179 as recoder
import pcp_uniform_affine_pair_units as history

execute=parent.execute
scalar=parent.scalar
PREFIX='hist__and__'


def rewrite(old, *, regroup=True):
    first=recoder.rewrite(old)
    second=history.rewrite(first,prefix=PREFIX)
    packet=dict(second)
    factors=list(first['unit_factors'])+second['unit_factors'][:-1]
    if regroup:
        private={n for n,_,_,_ in second['source']
                 if n.startswith('recoder_unit_product') or n.startswith(PREFIX+'history_unit_product')}
        assert len(private)==9
        assert all({n for n,_,a,b in second['source'] if key in (a,b)}<=private for key in private)
        source=[row for row in second['source'] if row[0] not in private]
        last=factors[0]
        for i,factor in enumerate(factors[1:]):
            name=f'complete_unit_product{i}'
            source.append((name,'*',last,factor));last=name
        old_pairs={(first['unit_register'],1),(second['unit_register'],1)}
        assert old_pairs<=set(second['comparisons'])
        pairs=[pair for pair in second['comparisons'] if pair not in old_pairs]
        pairs += [(second['unit_factors'][-1],1),(last,1)]
        packet.update(source=source,comparisons=pairs,unit_register=last,
                      unit_factors=factors)
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in packet['source'])
    assert len(packet['source'])==old['operations']+9
    assert counts==dict(M=old['multiplications']+9,A=old['additions_subtractions'])
    assert len(packet['comparisons'])==old['equations']-28
    assert len(packet['auxiliaries'])==old['witnesses']-19
    packet.update(regroup=regroup,raw_packet=old,recoder_stage=first,history_stage=second,
        native_prefixes=['geo__','and__',PREFIX],
        all_norm_factors=first['unit_factors'][:-1]+second['unit_factors'][:-1],
        recoder_unit_factors=first['unit_factors'],history_unit_factors=second['unit_factors'],
        equations=len(packet['comparisons']),witnesses=len(packet['auxiliaries']))
    return packet


def build(*args,regroup=True,**kwargs):return rewrite(parent.build(*args,**kwargs),regroup=regroup)
def odd_machine(*,regroup=True,**kwargs):return rewrite(parent.odd_machine(**kwargs),regroup=regroup)
def polynomial_source(packet):return history.polynomial_source(packet)


def ledger(packet):
    record={key:packet[key] for key in ('width','tiles','layout','inline_initial',
        'program_code','regroup','operations','multiplications','additions_subtractions',
        'equations','witnesses')}
    e=packet['equations']
    record['polynomial']=dict(operations=packet['operations']+3*e-1,
        multiplications=packet['multiplications']+e,
        additions_subtractions=packet['additions_subtractions']+2*e-1)
    return record


def lift(packet,values):
    middle=history.lift(packet['history_stage'],values)
    return recoder.lift(packet['recoder_stage'],middle)


def project(packet,values):
    first=recoder.project(packet['recoder_stage'],values,
                         execute(packet['raw_packet']['source'],values))
    return history.project(packet['history_stage'],first,
                           execute(packet['recoder_stage']['source'],first))


def audit_identity(packet,values):
    """Independent restored-parent residual formula, including strong corrections."""
    before=execute(packet['raw_packet']['source'],lift(packet,values))
    pairs=packet['raw_packet']['comparisons']
    rr={(a,b):scalar(a,before)-scalar(b,before) for a,b in pairs}
    first=packet['recoder_stage'];second=packet['history_stage']
    removed=set(first['removed_parent_comparisons'])|set(second['removed_parent_comparisons'])
    # Second-stage pairs use first-stage aliases.  Its retained comparisons
    # have no projected first-stage variables as direct endpoints.
    factors={}
    for prefix in packet['native_prefixes']:
        n=lambda value:prefix+value
        factors[n('R15')]=1+rr[(n('L15'),n('R15'))]
        factors[n('P17')]=(1+rr[(n('L17'),n('P17'))]
            -rr[(n('ic22'),n('R16'))]*before[n('aux_square_gap')])
        factors[n('first_unit')]=1-4*rr[(n('L9'),n('R9'))]
        if prefix!='geo__':factors[n('bs_q')]=1-rr[(n('bs_q'),n('q'))]
    raw_others=[r for pair,r in rr.items() if pair not in removed]
    # Every removed definition is exactly restored, including all three roots
    # as rational coordinates away from integer zeros.
    aliases=dict(first['projection_aliases'],**second['projection_aliases'])
    for key,value in aliases.items():
        pair=(key,value) if (key,value) in rr else (value,key)
        assert rr[pair]==0
    product=lambda names:__import__('functools').reduce(lambda a,b:a*factors[b],names,1)
    if packet['regroup']:
        expected_unit=product(packet['unit_factors'])
        expected_others=raw_others+[factors[PREFIX+'bs_q']-1]
    else:
        expected_unit=product(packet['history_unit_factors'])
        expected_others=raw_others+[product(packet['recoder_unit_factors'])-1]
    source,out=polynomial_source(packet);env=execute(source,values)
    assert all(env[name]==value for name,value in factors.items())
    assert [scalar(a,env)-scalar(b,env) for a,b in packet['comparisons'][:-1]]==expected_others
    assert env[packet['unit_register']]==expected_unit
    assert env[out]==expected_unit*(1+sum(r*r for r in expected_others))-1
    assert project(packet,lift(packet,values))==values


def degree_audit(packet):
    """Exact homogeneous bounds, with the one mandatory norm cancellation.

    For each projected core, d=X+ac+G, G=ga*(4a+3), so its main norm
    equals X²+2Xac+2XG+2acG+G²-(4a+3)c².  Its unique highest term is
    2acG.  We audit this identity's source prerequisites explicitly and
    use its degree bound; every other step uses literal circuit arithmetic.
    """
    variables=packet['parameters']+packet['auxiliaries']
    degree={n:1 for n in variables};top={n:1+i%3 for i,n in enumerate(variables)}
    for p in packet['native_prefixes']:
        top[p+'tau_gap']=1;top[p+'eta']=top[p+'zeta']=1
    d=lambda v:degree[v] if isinstance(v,str) else 0
    c=lambda v:top[v] if isinstance(v,str) else v
    rows={n:(op,a,b) for n,op,a,b in packet['source']}
    overrides={p+'R15':p for p in packet['native_prefixes']}
    for n,op,a,b in packet['source']:
        da,db=d(a),d(b)
        if op=='*':degree[n],top[n]=da+db,c(a)*c(b)
        else:
            degree[n]=max(da,db)
            ca=c(a) if da==degree[n] else 0;cb=c(b) if db==degree[n] else 0
            top[n]=ca+cb if op=='+' else ca-cb
        if n in overrides:
            p=overrides[n];X=p+'wn2';ac=p+'cam2';G=p+'gam';aa=p+'R12';cc=p+'R10a'
            assert rows[n]==('-',p+'L15',p+'Ac2')
            assert rows[p+'R14']==('+',p+'D1',G) and rows[p+'D1']==('+',X,ac)
            assert rows[ac]==('*',cc,aa) and rows[G]==('*',p+'ga',p+'a4m5')
            assert rows[p+'a4m5']==('+',p+'a4',3) and rows[p+'a4']==('*',4,aa)
            assert rows[p+'A']==('+',p+'a_square',p+'a4m5')
            assert rows[p+'a_square']==('*',aa,aa)
            assert rows[p+'c2']==('*',cc,cc)
            assert rows[p+'Ac2']==('*',p+'A',p+'c2')
            assert rows[p+'L15']==('*',p+'R14',p+'R14')
            highest=d(ac)+d(G)
            competitors=[2*d(X),d(X)+d(ac),d(X)+d(G),2*d(G),d(p+'a4m5')+2*d(cc)]
            assert highest>max(competitors)
            degree[n]=highest;top[n]=2*c(ac)*c(G)
    pair_degrees=[];pair_tops=[]
    for a,b in packet['comparisons'][:-1]:
        v=max(d(a),d(b));pair_degrees.append(v)
        pair_tops.append((c(a) if d(a)==v else 0)-(c(b) if d(b)==v else 0))
    maximum=max(pair_degrees)
    sos_top=sum(v*v for deg,v in zip(pair_degrees,pair_tops) if deg==maximum)
    assert sos_top>0
    unit=packet['unit_register'];coefficient=top[unit]*sos_top
    assert coefficient
    exact=d(unit)+2*maximum
    if packet['regroup']:
        e=2 if packet['program_code']=='parameter' else 1
        k=packet['width'];v=(k+1)*e+1
        nu=k*e+1 if packet['inline_initial'] else 2
        dd=packet['history_packet']['scale_exponent']*nu
        expected_factors=[5*e+7,6*e+12,3*e+5,5*v+7,10*v+8,3*v+5,v,
                          5*dd+7,12*dd-6*nu+8,3*dd+5]
        assert [d(n) for n in packet['unit_factors']]==expected_factors
        assert d(unit)==14*e+19*v+20*dd-6*nu+64
        assert maximum==4*max(dd,v)+10
        assert exact==14*e+19*v+20*dd-6*nu+84+8*max(dd,v)
    else:
        e=2 if packet['program_code']=='parameter' else 1
        k=packet['width'];v=(k+1)*e+1
        nu=k*e+1 if packet['inline_initial'] else 2
        dd=packet['history_packet']['scale_exponent']*nu
        assert exact==21*dd-6*nu+20+2*max(14*e+19*v+44,4*dd+10)
    blob=abs(coefficient).to_bytes((abs(coefficient).bit_length()+7)//8,'big')
    return dict(exact_degree=exact,unit_degree=d(unit),maximum_outer_degree=maximum,
        factor_degrees={n:d(n) for n in packet['recoder_unit_factors']+packet['history_unit_factors']},
        leading_sign=1 if coefficient>0 else -1,
        leading_bits=abs(coefficient).bit_length(),leading_sha256=hashlib.sha256(blob).hexdigest())


def verify():
    rng=random.Random(918193);cases=signed=0;records=[]
    tiles=(((0,),(1,)),((1,0),(0,1)))
    for width in (4,7):
      for layout in ('contiguous','interleaved'):
       for inline in (False,True):
        for code in (None,'parameter',4):
         for regroup in (False,True):
            packet=build(tiles,width,(2,3),(4,5),(5,2,6,4),layout=layout,
                         inline_initial=inline,program_code=code,regroup=regroup)
            source,_=polynomial_source(packet);rec=ledger(packet)
            assert len(source)==rec['polynomial']['operations']
            counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
            assert counts==dict(M=rec['polynomial']['multiplications'],A=rec['polynomial']['additions_subtractions'])
            assert len(source)==parent.ledger(packet['raw_packet'])['polynomial']['operations']-75
            for i in range(8):
                values={n:rng.randrange(1,5) if i<4 else rng.randrange(-2,4)
                        for n in packet['parameters']+packet['auxiliaries']}
                audit_identity(packet,values);cases+=1;signed+=i>=4
            records.append(dict(rec,degree_audit=degree_audit(packet)))
    for code in (None,'parameter',3):
        packet=build((((0,),(1,)),),100,(2,3),(4,5),(5,2,6,4),
                     layout='contiguous',inline_initial=False,program_code=code)
        records.append(dict(ledger(packet),degree_audit=degree_audit(packet)))
    samples=[]
    for layout in ('contiguous','interleaved'):
      for inline in (False,True):
       for regroup in (False,True):
        packet=odd_machine(layout=layout,inline_initial=inline,regroup=regroup)
        samples.append(dict(ledger(packet),degree_audit=degree_audit(packet)))
    example=odd_machine()
    return dict(status='PASS_GPCP_COMPLETE_FIXED_PROGRAM_UNITS',
        complete_output_identities=cases,signed_cases=signed,variant_ledgers=records,
        sample_ledgers=samples,example=dict(ledger=ledger(example),parameters=example['parameters'],
            auxiliaries=example['auxiliaries'],source=example['source'],comparisons=example['comparisons']),
        scope='Exact positive projection of the complete fixed-program compiler. Nine sign-safe norms share one checksum; the other checksum remains explicit. No numerical universal table is supplied and no universal75/88 improvement is asserted.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
