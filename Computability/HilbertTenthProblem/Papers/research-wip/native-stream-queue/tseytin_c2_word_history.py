"""A paid, fixed-arity C2 word-to-aaa predicate, preserving noninvertibility.

The sole positive parameter is a sentinel base-eight word code, not an
ordinary program/input loader.  Endpoints themselves reject invalid codes.
Every native and chronological constraint is inherited literally, with two
positive endpoint graph substitutions and guarded native transformations.
"""
import argparse
from collections import Counter, deque
from functools import lru_cache
from itertools import product
import hashlib
import json
from math import prod
from pathlib import Path
import random

import tseytin_group_completion_obstruction as primary
import gpcp_slope_class_compiler as planner
import pcp_affine_slope_class_history as history
import native_binary_positive_scale as scale
import native_binary_computed_fields as fields
import native_binary_norm_units as norms
import native_binary_index_coupled_units as coupled

ALPHABET = 'abcde'
SYMBOLS = ALPHABET+'#'
CODES = {c:i+1 for i,c in enumerate(SYMBOLS)}
RELATIONS = (('ac','ca'),('ad','da'),('bc','cb'),('bd','db'),
             ('eca','ce'),('edb','de'),('cdca','cdcae'),
             ('caaa','aaa'),('daaa','aaa'))
TILES = tuple((c,c) for c in SYMBOLS) + tuple(
    (u,v) for a,b in RELATIONS for u,v in ((a,b),(b,a)))
FORMS = ('raw','scaled','fields','units','coupled')
execute = scale.execute
scalar = history.scalar


def encode(word):
    """Sentinel code: enc(empty)=1; appending c multiplies by8 and adds c."""
    result=1
    for c in word:
        assert c in CODES
        result=8*result+CODES[c]
    return result


def raw(word):
    return encode(word)-8**len(word)


def decode(value):
    """Return the C2 word, or None for any invalid positive integer code."""
    if type(value) is not int or value<=0:return None
    digits=[]
    while value>=8:
        value,digit=divmod(value,8)
        if not 1<=digit<=5:return None
        digits.append(ALPHABET[digit-1])
    return ''.join(reversed(digits)) if value==1 else None


@lru_cache(None)
def _history():
    assert tuple(primary.C2)==RELATIONS and len(TILES)==24
    tiles=[(tuple(CODES[c] for c in u),tuple(CODES[c] for c in v)) for u,v in TILES]
    maps=history.parent.maps_from_tiles(tiles,3)
    packet=planner.choose_history(maps)
    assert packet['history_kind']=='slope_classes'
    assert packet['baselines']==(64,64) and packet['selected_products']==8
    assert packet['scale_exponent']==36 and packet['K']==65536
    return packet


def build(form='coupled'):
    assert form in FORMS
    h=_history()
    endpoint_rows=[('c2_initial_product','*',8,'word'),
                   ('c2_initial','+','c2_initial_product',6),
                   ('c2_terminal_product','*',4096,'Ufinal'),
                   ('c2_terminal','+','c2_terminal_product',3145)]
    aliases={'Vinitial':'c2_initial','Vfinal':'c2_terminal'}
    alias=lambda v:aliases.get(v,v) if isinstance(v,str) else v
    source=endpoint_rows+[(n,op,alias(a),alias(b)) for n,op,a,b in h['source']]
    packet=scale.metadata(dict(h,source=source,
        comparisons=[(alias(a),alias(b)) for a,b in h['comparisons']],
        parameters=['word'],auxiliaries=['Ufinal']+h['auxiliaries'],
        c2_word_history=True,c2_history_parent=h,c2_endpoint_aliases=aliases,
        public_registers=dict(initial='c2_initial',terminal='c2_terminal'),
        exact_degree=None,unit_product=False))
    scale.checked_source(source,packet['parameters'],packet['auxiliaries'])
    if form!='raw':packet=scale.rewrite(packet,'and__')
    if form in ('fields','units','coupled'):packet=fields.rewrite(packet,prefix='and__')
    if form in ('units','coupled'):packet=norms.rewrite(packet,normalized=True)
    if form=='coupled':packet=coupled.rewrite(packet)
    return dict(packet,form=form,positive_witnesses=len(packet['auxiliaries']),
        unit_product=bool(packet.get('native_norm_units')),
        input_contract='word=enc8(u); invalid encodings have no positive zero by the endpoint theorem',
        semantics='u equals aaa in the literal C2 semigroup; no program/input loader included')


def polynomial_source(packet,*,sum_of_squares=False):
    if packet.get('native_norm_units'):
        return norms.polynomial_source(packet,sum_of_squares=sum_of_squares)
    return scale.polynomial_source(packet)


def ledger(packet):
    result=norms.ledger(packet) if packet.get('native_norm_units') else scale.ledger(packet)
    return dict(form=packet['form'],**result)


def endpoint_lift(values):
    return {n:values[n] for n in _history()['auxiliaries']} | dict(
        Ufinal=values['Ufinal'],Vinitial=8*values['word']+6,
        Vfinal=4096*values['Ufinal']+3145)


def selected_words(selection):
    assert selection and all(type(i) is int and 0<=i<24 for i in selection)
    return tuple(''.join(TILES[i][j] for i in selection) for j in (0,1))


def one_step_selection(word,relation,direction,position):
    """Arbitrary-position rule, with both literal contexts copied and paid."""
    assert set(word)<=set(ALPHABET)
    assert type(relation) is int and 0<=relation<9 and direction in (0,1)
    before,after=RELATIONS[relation][::1 if direction==0 else -1]
    assert type(position) is int and 0<=position<=len(word)-len(before)
    assert word[position:position+len(before)]==before
    suffix=word[position+len(before):]
    selection=tuple(ALPHABET.index(c) for c in word[:position])+(6+2*relation+direction,)
    selection+=tuple(ALPHABET.index(c) for c in suffix)
    following=word[:position]+after+suffix
    assert selected_words(selection)==(word,following)
    return selection,following


def derivation_selection(initial,steps):
    """steps=(relation,direction,position); returns a literal finite tile word."""
    assert set(initial)<=set(ALPHABET)
    selection=[];word=initial
    for step in steps:
        if selection:selection.append(5)
        part,word=one_step_selection(word,*step);selection.extend(part)
    if not steps:selection=[ALPHABET.index(c) for c in initial]
    assert selection
    top,bottom=selected_words(selection)
    assert top+'#'+word==initial+'#'+bottom
    return tuple(selection),word


def recover_derivation(word,selection):
    """Exact string proof oracle; not a bounded search for semigroup equality."""
    top,bottom=selected_words(selection)
    assert top+'#aaa'==word+'#'+bottom
    chunks=[[]]
    for tile in selection:
        if tile==5:chunks.append([])
        else:chunks[-1].append(tile)
    current=word;steps=[]
    for chunk in chunks:
        source=''.join(TILES[i][0] for i in chunk)
        target=''.join(TILES[i][1] for i in chunk)
        assert source==current
        cursor=0
        for i in chunk:
            before,after=TILES[i]
            assert current[cursor:cursor+len(before)]==before
            if i>=6:
                steps.append((i//2-3,i%2,cursor))
                current=current[:cursor]+after+current[cursor+len(before):]
            cursor+=len(after)
        assert current==target
    assert current=='aaa'
    return steps


def outer_fixture(initial,steps,form='coupled'):
    selection,terminal=derivation_selection(initial,steps)
    assert terminal=='aaa'
    h=_history();U=1;V=8*encode(initial)+6
    beforeU=[];beforeV=[]
    for tile in selection:
        beforeU.append(U);beforeV.append(V)
        a,c,b,d=h['maps'][tile];U,V=a*U+c,b*V+d
    total=8*encode(initial)+6+U+V;D=1<<total.bit_length();B=h['K']*D
    pack=lambda digits:sum(v*B**j for j,v in enumerate(digits))
    v=dict(Ufinal=U,Vfinal=V,height_slack=D-total,H_U=pack(beforeU),H_V=pack(beforeV))
    for tile in range(24):v[f'Shat{tile}']=pack([int(i==tile) for i in selection])+1
    zsum=0
    for tag,groups,digits in (('U',h['groups_U'],beforeU),('V',h['groups_V'],beforeV)):
        for i,group in enumerate(groups):
            value=pack([v if tile in group['tiles'] else 0 for tile,v in zip(selection,digits)])+1
            v[f'Z{tag}hat{i}']=value;zsum+=value
    v['global_bound']=B**len(selection)-v['H_U']-v['H_V']-zsum
    assert v['Vfinal']==4096*v['Ufinal']+3145
    packet=build(form)
    values={n:v.get(n,1) for n in packet['parameters']+packet['auxiliaries']}
    values['word']=encode(initial)
    # Native coordinates are placeholders. Execute the actual complete outer
    # subgraph and check its joined AND, without pretending these are Pell zeros.
    outer=[row for row in packet['source'] if not row[0].startswith('and__')]
    env=execute(outer,values)
    assert all(scalar(a,env)==scalar(b,env) for a,b in packet['comparisons'][:3])
    I=h['interfaces']
    assert env[I['H']]&env[I['M']]==env[I['Z']]
    assert env[I['H']]<env[I['scale']] and env[I['M']]<env[I['scale']]
    assert min(values.values())>0
    return dict(input_word=initial,duration=len(selection),rewrite_steps=len(steps),
        rows=len(selection),form=form,full_Pell_witnesses_materialized=False)


def all_rule_fixture_paths():
    """Small actual paths to aaa covering each oriented relation at least once."""
    queue=deque([('aaa',[])]);seen={'aaa'};covered={}
    while queue and len(covered)<18:
        word,path=queue.popleft()
        if len(path)>=10:continue
        for relation,(a,b) in enumerate(RELATIONS):
          for direction,(before,after) in enumerate(((a,b),(b,a))):
           for position in range(len(word)-len(before)+1):
            if word[position:position+len(before)]!=before:continue
            new=word[:position]+after+word[position+len(before):]
            if len(new)>12:continue
            forward=path+[(relation,direction,position)]
            reverse=[(r,1-d,p) for r,d,p in reversed(forward)]
            covered.setdefault((relation,1-direction),(new,reverse))
            if new not in seen:seen.add(new);queue.append((new,forward))
    assert len(covered)==18
    return covered


def source_audit(cases=64):
    rng=random.Random(652913);p=build('raw');h=_history()
    source,out=polynomial_source(p)
    for j in range(cases):
        values={n:rng.randrange(1,6) if j<cases//2 else rng.randrange(-4,5)
                for n in p['parameters']+p['auxiliaries']}
        lifted=endpoint_lift(values)
        env=execute(source,values);old=execute(h['source'],lifted)
        assert all(env[n]==old[n] for n,_,_,_ in h['source'])
        residuals,face=history.manual(h,lifted)
        assert residuals==[scalar(a,env)-scalar(b,env) for a,b in p['comparisons']]
        assert env[out]==sum(r*r for r in residuals)
        if j<cases//2:assert min(lifted.values())>0
    scaled=build('scaled');computed=build('fields');unit=build('units');final=build()
    audits=dict(endpoint_raw=dict(complete_identities=cases,signed=cases//2),
        scaled=scale.identity_audit(scaled,cases,652914),
        computed=fields.audit(computed,cases,652915),
        units=norms.audit(unit,cases,652916),
        index=coupled.audit(final['coupled_parent'],cases,652917),
        coupled=coupled.audit(final,cases,652918))
    return audits


def word_audit():
    contexts=['']+list(ALPHABET)+[''.join(w) for w in product(ALPHABET,repeat=2)]
    steps=0
    for rel,(a,b) in enumerate(RELATIONS):
      for direction,(before,after) in enumerate(((a,b),(b,a))):
       for prefix in contexts:
        for suffix in contexts:
            initial=prefix+before+suffix
            selected,result=one_step_selection(initial,rel,direction,len(prefix))
            assert result==prefix+after+suffix
            A,C,B,D=_history()['maps'][selected[len(prefix)]]
            assert (A,C,B,D)==(8**len(before),raw(before),8**len(after),raw(after))
            assert encode(initial)==8**(len(before)+len(suffix))*encode(prefix)+8**len(suffix)*raw(before)+raw(suffix)
            steps+=1
    # Enumerate every selected word through length3 and solve its numerical
    # endpoint equation for its unique possible input.  Invalid inputs may
    # not be discarded before this calculation.
    candidate_count=accepted=invalid_positive=0
    for length in (1,2,3):
      for selection in product(range(24),repeat=length):
        candidate_count+=1
        top,bottom=selected_words(selection)
        numerator=encode(top+'#aaa')-raw(bottom)-6*8**len(bottom)
        denominator=8**(len(bottom)+1)
        value,remainder=divmod(numerator,denominator)
        if remainder or value<=0:continue
        decoded=decode(value)
        invalid_positive+=decoded is None
        assert decoded is not None
        recovered=recover_derivation(decoded,selection)
        check,_=derivation_selection(decoded,recovered)
        assert selected_words(check)[0]+'#aaa'==decoded+'#'+selected_words(check)[1]
        accepted+=1
    assert invalid_positive==0
    fixtures=[]
    for prefix in ('','c','d','cc','cd','dc','dd','cdc','dcd','ccdd'):
        word=prefix+'aaa'
        # Remove the rightmost c/d immediately before aaa, then repeat.
        rule_steps=[(7 if c=='c' else 8,0,len(prefix)-i-1)
                    for i,c in enumerate(reversed(prefix))]
        for form in ('raw','coupled'):
            fixtures.append(outer_fixture(word,rule_steps,form))
    oriented=all_rule_fixture_paths()
    fixtures += [outer_fixture(word,steps) for word,steps in oriented.values()]
    assert primary.neighbors('b',RELATIONS)==set() and decode(encode('b'))=='b'
    return dict(arbitrary_position_rule_cases=steps,
        exhaustive_selection_candidates=candidate_count,
        numerically_accepted_candidates=accepted,
        invalid_positive_endpoint_candidates=invalid_positive,
        outer_histories=fixtures,oriented_rules_in_actual_outer_histories=len(oriented),
        isolated_false_group_target='b')


def closure_and_degree(packet):
    records=[]
    for sos in ((False,True) if packet.get('native_norm_units') else (False,)):
        source,out=polynomial_source(packet,sum_of_squares=sos)
        scale.checked_source(source,packet['parameters'],packet['auxiliaries'])
        rows={n:(a,b) for n,_,a,b in source};live=set()
        def visit(n):
            if n not in rows or n in live:return
            live.add(n)
            for v in rows[n]:
                if isinstance(v,str):visit(v)
        visit(out);assert live==set(rows)
        counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
        degree=norms.degree_bound(packet,sum_of_squares=sos) if packet.get('native_norm_units') else scale.degree_bound(packet)
        records.append(dict(finalizer='SOS' if sos or not packet.get('native_norm_units') else 'product',
            operations=len(source),multiplications=counts['M'],additions_subtractions=counts['A'],degree=degree))
    return records


def verify():
    packet=build();source,out=polynomial_source(packet)
    ledgers=[ledger(build(form)) for form in FORMS]
    assert ledgers[-1]['product']['operations']==374
    assert (packet['operations'],packet['equations'],packet['witnesses'])==(357,6,52)
    return dict(status='PASS_TSEYTIN_C2_WORD_HISTORY',primary_url=primary.PRIMARY,
        fixed_relations=RELATIONS,fixed_tiles=TILES,fixed_maps=_history()['maps'],
        history_baselines=_history()['baselines'],history_candidates=_history()['history_candidates'],
        ledgers=ledgers,closure_degree=[closure_and_degree(build(form)) for form in FORMS],
        algebra_checks=source_audit(),word_checks=word_audit(),
        default=dict(source=source,output=out,comparisons=packet['comparisons'],
            parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
            source_sha256=hashlib.sha256(json.dumps(source).encode()).hexdigest()),
        scope='Complete fixed-arity unbounded C2 word-to-aaa relation on all positive sentinel-code inputs. No ordinary program/input loader, numerical universal input bound, or complete Pell fixture is claimed.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['ledgers'][-1])
