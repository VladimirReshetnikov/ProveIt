"""Fresh, one-use metadata composition of two already proved integer identities.
Reads frozen JSON as records only. Never run/import after the first receipt.
"""
from pathlib import Path
import collections
import hashlib
import json

BASE=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
INPUT=BASE/'positive7_repeated_pack_compiler_root.json'
PIN='2fd115c545d412be63b469023b8e13da68648dc79ead5086df2f0aaac6b6377a'
OUTPUT=Path('/tmp/positive7_left_scale_compiler_root.json')
assert not OUTPUT.exists()
payload=INPUT.read_bytes()
assert hashlib.sha256(payload).hexdigest()==PIN
previous=json.loads(payload)

def digest(value):
    return hashlib.sha256(json.dumps(value,separators=(',',':')).encode()).hexdigest()

def operations(records):
    tally=collections.Counter(item[1] for item in records)
    assert set(tally)<={'+','-','*'}
    return {'M':tally['*'],'A':tally['+']+tally['-'],'operations':len(records)}

def successor(old):
    r,m,ell=old['r'],old['m'],old['ell']
    assert r>=1 and m==8+2*r and ell==62+6*r
    parts={};cursor=0
    for key,stats in old['stages'].items():
        parts[key]=old['source'][cursor:cursor+stats['operations']]
        assert operations(parts[key])==stats
        cursor+=stats['operations']
    assert cursor==len(old['source'])
    emitted=[];partition={};kept=[];rebounds=[];stage=''
    def gate(name,kind,left,right):
        record=[name,kind,left,right]
        emitted.append(record);partition.setdefault(stage,[]).append(record)
        return name
    def copy(records,rebind=None):
        rebind=rebind or {}
        for record in records:
            name,kind,left,right=record
            a=rebind.get(left,left) if isinstance(left,str) else left
            b=rebind.get(right,right) if isinstance(right,str) else right
            gate(name,kind,a,b)
            if a==left and b==right:kept.append(name)
            else:rebounds.append({'before':record,'after':[name,kind,a,b]})
    prefix_keys=list(parts)[:list(parts).index('two_upper_horner_packs')]
    for key in prefix_keys:
        stage=key;copy(parts[key])
    P=old['ports']['P'];Pm=old['ports']['selector_power']
    old_high=[row for row in parts['two_upper_horner_packs'] if row[0].startswith('left_')]
    other_high=[row for row in parts['two_upper_horner_packs'] if row[0].startswith('output_')]
    assert len(old_high)+len(other_high)==len(parts['two_upper_horner_packs'])
    assert operations(old_high)==dict(M=53+4*r,A=53+4*r,operations=106+8*r)
    assert operations(other_high)==dict(M=52+4*r,A=52+4*r,operations=104+8*r)
    stage='repeated_high_left_pack'
    p4=gate('left_support_P4','*','scale_square_0','scale_square_0')
    p5=gate('left_support_P5','*','scale_square_0','pack_P3')
    p12=gate('left_support_P12','*','pack_P6','pack_P6')
    p14=gate('left_support_P14','*','pack_P7','pack_P7')
    p28=gate('left_support_P28','*',p14,p14)
    u4=gate('left_pair_factor_2','+',1,'scale_square_0')
    u6=gate('left_pair_factor_6','+',1,'pack_P6')
    u7=gate('left_pair_factor_7','+',1,'pack_P7')
    u14=gate('left_pair_factor_14','+',1,p14)
    g7=gate('left_four_seven_factor','*',u7,u14)
    history='H_7';intermediate={}
    for i in range(6,0,-1):
        history=gate('left_history_shift_'+str(i),'*',history,P)
        history=gate('left_history_join_'+str(i),'+',history,'H_'+str(i))
        intermediate[i]=history
    difference=gate('left_short_history_difference','-',intermediate[6],'H_7')
    correction=gate('left_short_history_correction','*',p5,difference)
    b6b=gate('left_short_history_b','-',history,correction)
    top=gate('left_high_tail_shift','*',old['ports']['D'],P)
    acc=gate('left_high_tail','+',top,old['ports']['S'])
    for j in range(r-1,-1,-1):
        f1,f2=old['centered_input_forms'][str(j)]
        small=gate('left_form_shift_'+str(j),'*',P,f2)
        small=gate('left_form_pair_'+str(j),'+',small,f1)
        repeated=gate('left_form_repeated_'+str(j),'*',u4,small)
        upper=gate('left_form_high_shift_'+str(j),'*',p4,acc)
        acc=gate('left_form_high_join_'+str(j),'+',upper,repeated)
    repeated=gate('left_seven_repeated','*',g7,history)
    upper=gate('left_seven_high_shift','*',p28,acc)
    acc=gate('left_seven_high_join','+',upper,repeated)
    for label,block in [('b',b6b),('a',intermediate[2])]:
        repeated=gate('left_six_repeated_'+label,'*',u6,block)
        upper=gate('left_six_high_shift_'+label,'*',p12,acc)
        acc=gate('left_six_high_join_'+label,'+',upper,repeated)
    left_exit=acc
    assert operations(partition[stage])==dict(M=20+3*r,A=16+2*r,operations=36+5*r)
    stage='upper_output_horner_pack';copy(other_high)
    stage='factored_pack_joins'
    copy(parts[stage],{'left_join_'+str(m):left_exit})
    old_scale=parts['fixed_native_power_after_shared_square']
    assert 'scale_square_0' not in {row[0] for row in old_scale}
    assert operations(old_scale)==dict(M=old['power_cost']-1,A=0,operations=old['power_cost']-1)
    stage='shared_native_scale'
    p19=gate('native_shared_P19','*',p12,'pack_P7')
    mid=gate('native_shared_m_plus_19','*',Pm,p19)
    squared=gate('native_shared_double','*',mid,mid)
    scale=gate('native_shared_scale','*',Pm,squared)
    stage='complete_native64';copy(parts[stage],{old['ports']['T']:scale})
    for key in list(parts)[list(parts).index('complete_native64')+1:]:
        stage=key;copy(parts[key])
    assert [item['after'][0] for item in rebounds]==['left_selector_shift','pell_q']
    removed=old_high+old_scale;removed_names={row[0] for row in removed}
    supplied=['x']+old['positive_auxiliaries'];known=set(supplied);edges={};roles=set()
    assert len(supplied)==len(known)
    for name,kind,a,b in emitted:
        assert name not in known and kind in ('+','-','*')
        for v in (a,b):
            if isinstance(v,str):assert v in known and v not in removed_names,(name,v)
            elif isinstance(v,dict):assert set(v)=={'fixed'};roles.add(v['fixed'])
            else:assert type(v) is int
        known.add(name);edges[name]=(a,b)
    live=set();pending=[old['output']]
    while pending:
        v=pending.pop()
        if isinstance(v,str) and v not in live:
            live.add(v);pending.extend(edges.get(v,()))
    assert set(edges)<=live and set(supplied)<=live
    assert roles==set(old['static_checks']['named_fixed_roles']) and len(roles)==6+18*r
    assert len(old['comparisons'])==23 and len(supplied)-1==96+6*r
    assert emitted[-68:]==parts['single_polynomial_finalizer']
    gm,ga=old['geometric_extension']['M'],old['geometric_extension']['A']
    poly,cert=operations(emitted),operations(emitted[:-68])
    assert poly==dict(M=224+33*r+gm,A=504+44*r+ga,operations=728+77*r+gm+ga)
    assert cert==dict(M=201+33*r+gm,A=459+44*r+ga,operations=660+77*r+gm+ga)
    changed={'source','stages','ports','power_cost','pack_splice','static_checks','polynomial_ledger','certificate_ledger','certificate_prefix_rows'}
    result={k:v for k,v in old.items() if k not in changed}
    result['ports']=dict(old['ports'],T=scale,high_left_pack=left_exit,left_support_P12=p12)
    result['native_scale_products']=4
    result['parent_binary_power_cost']=old['power_cost']
    result.update(source=emitted,stages={key:operations(value) for key,value in partition.items()},polynomial_ledger=poly,certificate_ledger=cert,certificate_prefix_rows=len(emitted)-68,static_checks=dict(topology=True,all_computed_live=True,all_supplied_live=True,named_fixed_roles=sorted(roles)))
    result['left_scale_splice']=dict(removed_rows=removed,removed_digest=digest(removed),literal_retained_row_names=kept,rebound_rows=rebounds,old_source_digest=digest(old['source']),new_source_digest=digest(emitted),new_left_exit=left_exit,new_scale_exit=scale,new_left_ledger=operations(partition['repeated_high_left_pack']),native_scale_ledger=operations(partition['shared_native_scale']),finalizer_literal_equal=True,comparisons_literal_equal=True,positive_auxiliaries_literal_equal=True)
    return result

examples=[successor(old) for old in previous['examples']]
assert [g['r'] for g in examples]==[1,2,4]
receipt={'status':'FROZEN first metadata-only joint composition; never replay','emitter_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'inputs':[dict(path=str(INPUT),sha256=PIN,bytes=len(payload))],'generic_ledger':dict(domain='r>=1',certificate='(201+33r+gM(8+2r))M+(459+44r+gA(8+2r))A',polynomial='(224+33r+gM(8+2r))M+(504+44r+gA(8+2r))A',operations='728+77r+gM(8+2r)+gA(8+2r)',native_scale_products=4,witnesses='96+6r',equations=23,fixed_roles='6+18r',geometric_cost=previous['generic_ledger']['geometric_cost']),'fixed_data_recipe':previous['fixed_data_recipe'],'r0_fallback':previous['r0_fallback'],'examples':examples,'execution_scope':'Constructed/compared/count-labelled inert records and checked dependencies/liveness only. No saved scientific/helper execution or import, no source/coefficient arithmetic, degree propagation, numerical sampling or build.'}
OUTPUT.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(dict(output=str(OUTPUT),sha256=hashlib.sha256(OUTPUT.read_bytes()).hexdigest(),saved_rows=sum(len(g['source']) for g in examples),examples=[dict(r=g['r'],ledger=g['polynomial_ledger'],witnesses=g['witnesses']) for g in examples]),indent=2))
