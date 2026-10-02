"""Permute positive C2 digits to save one multiplication after zero-a388.

Literal words are unchanged; program numerals, copies and histories are
recompiled. Equivalence is existential input projection, not tuple identity.
"""
import argparse
from collections import Counter
from copy import deepcopy
from functools import lru_cache
import hashlib
from itertools import product
import json
from math import prod
from pathlib import Path
import random

import tseytin_zero_a388 as parent

scale=parent.scale
execute=parent.execute
loader=parent.loader
literal=parent.literal
CODES=dict(a=0,b=3,c=1,d=2,e=4,**{'#':5})
TILES=tuple((c,c) for c in '#ebdca')+tuple(literal.TILES[6:])
ALIASES={'linear_coefficient__363':'linear_group__362',
         'linear_sum__404':'linear_sum__403','linear_sum__423':'linear_sum__422'}
ADDED=[('permuted_delta_U','*',3,'Shat14'),('permuted_delta_V','*',3,'Shat15')]
REQUIRED={
 'linear_coefficient__363':('*','linear_group__362',2),
 'linear_group__393':('+','Shat13','Shat7'),
 'linear_coefficient__394':('*','linear_group__393',14),
 'linear_coefficient__395':('*','Shat9',21),
 'linear_coefficient__396':('*','Shat11',7),
 'linear_sum__404':('+','linear_coefficient__396','linear_sum__403'),
 'linear_coefficient__397':('-','linear_coefficient__398','Shat14'),
 'linear_coefficient__398':('*',253,'group_sum__221'),
 'linear_group__412':('+','Shat12','Shat6'),
 'linear_coefficient__413':('*','linear_group__412',14),
 'linear_coefficient__414':('*','Shat8',21),
 'linear_coefficient__415':('*','Shat10',7),
 'linear_sum__423':('+','linear_coefficient__415','linear_sum__422'),
 'linear_coefficient__416':('-','linear_coefficient__417','Shat15'),
 'linear_coefficient__417':('*',253,'group_sum__228'),
 'c2_shared_update_offset':('-','linear_sum__391',51504)}


def raw(word):
    v=0
    for c in word:v=8*v+CODES[c]
    return v


def encode(word):return 8**len(word)+raw(word)


def maps():return [(8**len(a),raw(a),8**len(b),raw(b)) for a,b in TILES]


@lru_cache(None)
def coefficients():
    # The literal suffix uses only a,b, with a=0 retained and b tripled.
    return tuple(3*c for c in parent.coefficients())


def fused_coefficients():
    h=[8*c for c in coefficients()];h[0]+=5*loader.DENOMINATOR
    return tuple(h)


def program_parameter(S):
    assert S and set(S)<=set('cd'),'literal primary program word required'
    A=8*(loader.DENOMINATOR*8**17*encode(S)+coefficients()[6])
    assert A>0
    return A


def changes(old):
    rows={n:(o,a,b) for n,o,a,b in old['source']}
    change={
     'linear_group__393':('+','Shat7','Shat12'),
     'linear_coefficient__394':('*','linear_group__393',7),
     'linear_coefficient__395':('*','linear_coefficient__396',14),
     'linear_coefficient__396':('+','Shat9','Shat10'),
     'linear_group__412':('+','Shat6','Shat13'),
     'linear_coefficient__413':('*','linear_group__412',7),
     'linear_coefficient__414':('*','linear_coefficient__415',14),
     'linear_coefficient__415':('+','Shat8','Shat11'),
     'linear_coefficient__398':('*',255,'group_sum__221'),
     'linear_coefficient__397':('-','linear_coefficient__398','permuted_delta_U'),
     'linear_coefficient__417':('*',255,'group_sum__228'),
     'linear_coefficient__416':('-','linear_coefficient__417','permuted_delta_V'),
     'linear_coefficient__399':('*','Shat19',4540),
     'linear_coefficient__418':('*','Shat18',4540),
     'linear_coefficient__400':('*','Shat20',512),
     'linear_coefficient__419':('*','Shat21',512),
     'linear_coefficient__401':('*','Shat22',1024),
     'linear_coefficient__420':('*','Shat23',1024),
     'c2_shared_update_offset':('-','linear_sum__391',45194)}
    for i,c in zip((365,367,369,371,373,375),(2,11,19,12,20,648)):
        n=f'linear_coefficient__{i}';o,a,b=rows[n];change[n]=(o,a,c)
    h=fused_coefficients()
    for n,i in [('query_degree4',4),('query_degree3',3),('query_degree1',1),('query_numerator',0)]:
        change[n]=('-',rows[n][1],-h[i])
    return change


def rewrite(old):
    merge=old.get('merge_units')
    assert type(merge) is bool and old==parent.build(merge_units=merge),'complete canonical zero-a388 parent required'
    rows={n:(o,a,b) for n,o,a,b in old['source']}
    assert all(rows.get(n)==r for n,r in REQUIRED.items()),'literal private selector arithmetic required'
    for n,expected in {'linear_coefficient__363':{'linear_sum__385'},
                       'linear_sum__404':{'linear_sum__405'},
                       'linear_sum__423':{'linear_sum__424'}}.items():
        assert {r for r,_,a,b in old['source'] if n in (a,b)}==expected,'private gate gained a consumer'
    change=changes(old);source=[]
    for n,o,a,b in old['source']:
        if n in ALIASES:continue
        o,a,b=change.get(n,(o,a,b))
        source.append((n,o,ALIASES.get(a,a),ALIASES.get(b,b)))
    source+=ADDED
    source=scale.sort_source(source,old['parameters']+old['auxiliaries'])
    scale.checked_source(source,old['parameters'],old['auxiliaries'])
    keys=('parameters','auxiliaries','comparisons','ordinary_comparisons',
          'unit_register','word_unit_register','power_unit_register',
          'word_factors','power_factors','merge_units','interfaces')
    p=scale.metadata(dict({k:deepcopy(old[k]) for k in keys},source=source,
        permuted_digits_parent=old,permuted_digits=True,letter_codes=CODES,tiles=TILES,
        program_recipe='A=8*(d*8^17*enc_new(S)+h6_new), d=8^64−1, digits a,b,c,d,e,#=0,3,1,2,4,5; S is the original valid literal primary program word; h_new=3*zero_a388.coefficients().',
        positive_integer_domain=True,identical_complete_polynomial=False,
        identical_positive_zero_set=False,positive_zero_bijection=False,
        projection='On recompiled valid program slices, I=8*enc_new(query)+5. Copies are #,e,b,d,c,a; relations6..23 retain their literal meaning. Recode histories and rebuild positive native extensions to preserve the universal accepted-input relation.'))
    assert p['operations']==old['operations']-1
    assert p['multiplications']==old['multiplications']-1
    assert p['additions_subtractions']==old['additions_subtractions']
    before=parent.maps();after=maps()
    assert all(a[0]==b[0] and a[2]==b[2] for a,b in zip(before,after))
    assert all(a>0 and b>0 and c>=0 and d>=0 and max(a+c,b+d)<65536 for a,c,b,d in after)
    return p


@lru_cache(None)
def build(*,merge_units=True):return rewrite(parent.build(merge_units=merge_units))


def checked_packet(p):
    assert p==build(merge_units=p['merge_units']),'complete canonical permuted-digits387 packet required'


def polynomial_source(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    checked_packet(packet)
    return literal.norms.polynomial_source(packet,sum_of_squares=sum_of_squares)


def degree_dictionary(packet):
    checked_packet(packet)
    return parent.degree_helper.degree_dictionary(dict(packet,word_strong_normalized=True))


def degree_bound(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    source,out=polynomial_source(packet,sum_of_squares=sum_of_squares)
    deg=degree_dictionary(packet);d=lambda v:deg[v] if isinstance(v,str) else 0
    for n,o,a,b in source:
        if n not in deg:deg[n]=d(a)+d(b) if o=='*' else max(d(a),d(b))
    return dict(degree_upper_bound=deg[out],word_factor_degree_bounds=[d(f) for f in packet['word_factors']],
        power_factor_degrees=[d(f) for f in packet['power_factors']],
        maximum_ordinary_residual_degree=max(max(d(a),d(b)) for a,b in packet['ordinary_comparisons']),
        exact_degree_claimed=False)


def ledger(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    source,out=polynomial_source(packet,sum_of_squares=sum_of_squares);c=Counter(o for _,o,_,_ in source)
    return dict(certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(source),multiplications=c['*'],additions_subtractions=c['+']+c['-'],output=out,
                        **degree_bound(packet,sum_of_squares=sum_of_squares)))


def actual_update(values,tag):
    k=0 if tag=='U' else 2;actual=maps()
    slopes=list(dict.fromkeys(r[k] for r in actual if r[k]!=64))
    return 64*values['H_'+tag]+sum((a-64)*(values[f'Z{tag}hat{i}']-1) for i,a in enumerate(slopes))+sum(r[k+1]*(values[f'Shat{i}']-1) for i,r in enumerate(actual))


def modified_parent(source,values):
    """Override entire updates and query coefficients, not old-polynomial identity."""
    e=dict(values);h=fused_coefficients();indices={'query_degree4':4,'query_degree3':3,'query_degree1':1,'query_numerator':0}
    for n,o,a,b in source:
        if n=='linear_constant__411':e[n]=actual_update(values,'U');continue
        if n=='linear_constant__430':e[n]=actual_update(values,'V');continue
        x=e[a] if isinstance(a,str) else a;y=-h[indices[n]] if n in indices else e[b] if isinstance(b,str) else b
        e[n]=x*y if o=='*' else x+y if o=='+' else x-y
    return e


def source_audit(cases=96):
    rng=random.Random(387389);counts=Counter()
    for merge in (False,True):
      p=build(merge_units=merge);old=p['permuted_digits_parent']
      for case in range(cases):
        signed=case>=cases//2
        v={n:rng.randrange(-4,5) if signed else rng.randrange(1,5) for n in p['parameters']+p['auxiliaries']}
        if case%16==0:v.update({f'Shat{i}':1 for i in range(24)});counts['zero_selector_contexts']+=1
        e=execute(p['source'],v);other=modified_parent(old['source'],v)
        for n,_,_,_ in p['source']:
            if n.startswith(('linear','permuted_')) or n=='c2_shared_update_offset':continue
            assert e[n]==other[n]
        counts['retained_nonupdate_register_maps']+=1;counts['signed_maps']+=signed
        for tag,out in [('U','linear_constant__411'),('V','linear_constant__430')]:
            assert e[out]==actual_update(v,tag);counts['actual_24_tile_update_identities']+=1
        assert e['linear_sum__384']==sum((5-i)*v[f'Shat{i}'] for i in range(6))
        for sos in (False,True):
            ns,no=polynomial_source(p,sum_of_squares=sos);os,oo=parent.polynomial_source(old,sum_of_squares=sos)
            env=execute(ns,v);assert env[no]==modified_parent(os,v)[oo]
            at=lambda a:env[a] if isinstance(a,str) else a
            S=sum((at(a)-at(b))**2 for a,b in p['ordinary_comparisons'])
            W=prod(env[n] for n in p['word_factors']);P=prod(env[n] for n in p['power_factors'])
            expected=(W*P-1)**2+S if merge and sos else W*P*(1+S)-1 if merge else (W-1)**2+(P-1)**2+S if sos else W*(1+S+(P-1)**2)-1
            assert env[no]==expected
            counts['complete_modified_parent_and_manual_finalizer_outputs']+=1;counts['signed_outputs']+=signed
    return dict(counts)


def query_audit():
    d=loader.DENOMINATOR;h=coefficients();g=fused_coefficients();count=0
    assert h[2]==h[5]==0 and h[6]>0 and all(g[i]<0 for i in (0,1,3,4))
    for rank in (2,3,5):
      for relators in ((),((1,2,-1,-2),)):
        S=loader.program_word(rank,relators);A=program_parameter(S)
        for x in range(1,17):
            word=loader.query_word(S,x);I=encode(word+'#');Q=8**(32*x)
            assert 'aaa' not in word and set(S)<=set('cd')
            assert d*I==A*Q**6+sum(g[i]*Q**i for i in (0,1,3,4))
            assert max(map(len,bin(I)[2:].split('1')))<=10
            count+=1
    old=parent.query_audit()['negative_power_branch_residues'];res=[]
    for parity in (0,1):
        Q=pow(8**32,parity,d)*pow(16,-1,d)%d
        r=sum(g[i]*pow(Q,i,d) for i in (0,1,3,4,6))%d
        assert r==3*old[parity] and 0<r<d;res.append(r)
    return dict(literal_query_cases=count,tail_coefficients=h,fused_coefficients=g,denominator=d,
        negative_power_branch_residues=res,zero_run_bound=10,
        residue_identity='New fused tail polynomial =3*zero_a388 fused tail polynomial−10d; valid program leading residues triple modulo d.')


def encoding_audit():
    seen=set();contextual=0
    for length in range(6):
      for chars in product(CODES,repeat=length):
        code=encode(''.join(chars));assert code not in seen;seen.add(code)
    for k,(a,b) in enumerate(literal.RELATIONS):
      for direction in (0,1):
       for left,right in [('',''),('a','b'),('ed','c'),('aaa','bb')]:
        start=left+(b if direction else a)+right
        old_selection,end=literal.derivation_selection(start,[(k,direction,len(left))])
        selection=[next(j for j,t in enumerate(TILES[:6]) if t==literal.TILES[i]) if i<6 else i for i in old_selection]
        top=''.join(TILES[i][0] for i in selection);bottom=''.join(TILES[i][1] for i in selection)
        assert top+'#'+end==start+'#'+bottom
        U,V=1,encode(start+'#')
        for i in selection:
            aa,cc,bb,dd=maps()[i];U,V=aa*U+cc,bb*V+dd
        assert U==encode(top) and V==encode(start+'#'+bottom)
        contextual+=1
    return dict(injective_sentinel_codes=len(seen),actual_contextual_rewrites=contextual)


def packed_history_audit():
    p=build();outer=[r for r in p['source'] if not r[0].startswith(('and__','exp__','query_','c2_power_'))]
    actual=maps();classes={tag:list(dict.fromkeys(row[k] for row in actual if row[k]!=64)) for tag,k in [('U',0),('V',2)]}
    count=Counter()
    for length in range(5):
      for letters in product('cd',repeat=length):
        prefix=''.join(letters);current=prefix;selection=[]
        if not current:selection=[5,5,5]
        while current:
            selection += [4 if c=='c' else 3 for c in current[:-1]]+[20 if current[-1]=='c' else 22]
            current=current[:-1]
            if current:selection.append(0)
        start=prefix+'aaa';U,V=1,encode(start+'#');us=[];vs=[]
        for i in selection:
            us.append(U);vs.append(V);a,c,b,d=actual[i];U,V=a*U+c,b*V+d
        assert V==4096*U+2560
        D=1<<max([U,V]+us+vs).bit_length();B=65536*D;P=B**len(selection)
        pack=lambda digits:sum(v*B**j for j,v in enumerate(digits))
        values={n:1 for n in p['parameters']+p['auxiliaries']}
        values.update(c2_initial=encode(start+'#'),Ufinal=U,height_slack=D,H_U=pack(us),H_V=pack(vs))
        for i in range(24):values[f'Shat{i}']=1+pack([int(tile==i) for tile in selection])
        for tag,k,digits in [('U',0,us),('V',2,vs)]:
            for j,a in enumerate(classes[tag]):values[f'Z{tag}hat{j}']=1+pack([v if actual[i][k]==a else 0 for i,v in zip(selection,digits)])
        values['global_bound']=P-values['H_U']-values['H_V']-sum(values[f'Z{tag}hat{j}'] for tag in 'UV' for j in range(4))
        assert values['global_bound']>0
        e=execute(outer,values)
        assert e['global_lhs__40']==e['P__30']==P
        assert e['U_lhs__151']==e['U_rhs__155'] and e['V_lhs__153']==e['V_rhs__157']
        assert e['joined_H__287']&e['joined_M__293']==e['joined_Z__294']
        assert e['linear_constant__411']==pack(us[1:]+[U])<P
        assert e['linear_constant__430']==pack(vs[1:]+[V])<P
        count['accepting_packed_histories']+=1;count['histories_with_delimiter']+=int(0 in selection);count['tile_steps']+=len(selection)
    return dict(count,scope='Actual packed outer histories and comparisons, not full native Pell-zero tuples or actual program queries.')


def guards():
    old=parent.build();bad=[]
    for n in REQUIRED:
        bad.append(dict(old,source=[(r,o,a,0 if r==n else b) for r,o,a,b in old['source']]))
    for n in ALIASES:
        bad.append(dict(old,source=old['source']+[('leak','+',n,1)]))
        bad.append(dict(old,interfaces=dict(old['interfaces'],nested={n:n})))
    bad += [dict(old,comparisons=[]),dict(old,program_recipe='arbitrary'),dict(old,tiles=literal.TILES)]
    for candidate in bad:
        try:rewrite(candidate)
        except (AssertionError,KeyError,TypeError):pass
        else:raise AssertionError('mutated parent accepted')
    total=len(bad)
    for key,value in [('letter_codes',parent.CODES),('tiles',parent.TILES),('projection','same tuple'),('source',build()['source'][:-1])]:
      for api in (polynomial_source,degree_dictionary,degree_bound):
        try:api(dict(build(),**{key:value}))
        except (AssertionError,KeyError,TypeError):pass
        else:raise AssertionError('mutated successor accepted')
        total+=1
    return total


def verify():
    records=[]
    for merge in (False,True):
      for sos in (False,True):
        p=build(merge_units=merge);rows,out=polynomial_source(p,sum_of_squares=sos);rec=ledger(p,sum_of_squares=sos)
        assert len(rows)==(387 if merge else 389) and rec['polynomial']['multiplications']==179
        assert p['operations']==(373 if merge else 372) and p['witnesses']==62 and p['equations']==(5 if merge else 6)
        parent.fusion.baseline.closure(rows,out,p['parameters']+p['auxiliaries'])
        before=parent.degree_dictionary(p['permuted_digits_parent']);after=degree_dictionary(p)
        assert all(after[n]==d for n,d in before.items() if n not in ALIASES)
        assert all(after[n]==1 for n,_,_,_ in ADDED)
        rec.update(merge_units=merge,sum_of_squares=sos,source=rows,output=out,
            parameters=p['parameters'],auxiliaries=p['auxiliaries'],comparisons=p['comparisons'],
            source_sha256=hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest())
        records.append(rec)
    return dict(status='PASS_TSEYTIN_PERMUTED_DIGITS387',forms=records,
        source_audit=source_audit(),query=query_audit(),encoding=encoding_audit(),
        packed_histories=packed_history_audit(),rejected_callers=guards(),
        scope='Universal accepted ordinary inputs on recompiled valid program slices. New numeral encoding and copy permutation; no same-tuple polynomial or positive-zero equivalence with388 claimed.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['source_audit']);print(result['packed_histories'])
