"""Fresh independent literal-source alias audit. One run, then permanent freeze.
Only record comparisons, labels, hashes, fanout, topology and count metadata.
Never evaluate a stored arithmetic instruction or import a saved helper.
"""
from pathlib import Path
from collections import Counter, defaultdict
import hashlib
import json

RECEIPT = Path('/tmp/positive7_power_alias_static_audit_riemann.json')
if RECEIPT.exists():
    raise RuntimeError('Do not replay: first receipt exists')

def demand(test, reason):
    if not test:
        raise ValueError(reason)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def digest(value):
    return sha(json.dumps(value,separators=(',',':')).encode())

def census(rows):
    c=Counter(row[1] for row in rows)
    demand(set(c)<= {'+','-','*'}, 'operator census')
    return dict(M=c['*'],A=c['+']+c['-'],operations=len(rows))

paths = [('positive7_shared_decoder_compiler_root.json','e6539f0c8b8d66b53537d228425932a0a3d030e78d5f96be0d68d513ebe20b95'),('positive7_power_alias_compiler_root.json','e2985ae7fa1754c347261bca096c4d360f263bcbabf58481f7a0e1d305558b2a')]
packets=[];pins=[]
for name,pin in paths:
    path=Path('/tmp')/name;raw=path.read_bytes()
    demand(sha(raw)==pin,'immutable input SHA')
    packets.append(json.loads(raw));pins.append(dict(path=str(path),sha256=pin,bytes=len(raw)))
old_packet,new_packet=packets
# Independent maps for the ACTUALLY SAVED examples only. No synthetic B/C parents.
maps={1:{'left_support_P4':'geom_P4','left_pair_factor_2':'geom_factor_4','left_support_P5':'geom_P5'},2:{'left_support_P12':'geom_P12','left_pair_factor_6':'geom_factor_12'},4:{'left_support_P4':'geom_P4','left_pair_factor_2':'geom_factor_4'}}
removed_definitions={
 'left_support_P4':['left_support_P4','*','scale_square_0','scale_square_0'],
 'left_pair_factor_2':['left_pair_factor_2','+',1,'scale_square_0'],
 'left_support_P5':['left_support_P5','*','scale_square_0','pack_P3'],
 'left_support_P12':['left_support_P12','*','pack_P6','pack_P6'],
 'left_pair_factor_6':['left_pair_factor_6','+',1,'pack_P6']}
target_definitions={
 'geom_P4':['geom_P4','*','scale_square_0','scale_square_0'],
 'geom_factor_4':['geom_factor_4','+','scale_square_0',1],
 'geom_P5':['geom_P5','*','geom_P4','lane_scale'],
 'geom_P12':['geom_P12','*','pack_P6','pack_P6'],
 'geom_factor_12':['geom_factor_12','+','pack_P6',1]}
demand(list(maps)==[g['r'] for g in new_packet['examples']]==[g['r'] for g in old_packet['examples']], 'saved graph index')
demand(set(new_packet)==set(old_packet),'top-level schema')
demand(new_packet['fixed_data_recipe']==old_packet['fixed_data_recipe'] and new_packet['r0_fallback']==old_packet['r0_fallback'],'fixed recipe and fallback unchanged')
demand(new_packet['emitter_sha256']=='55e8e002fc1988f54b050748e09be1a5d23a8f9aa5ffd176e1da90b06993872a','author code hash')
demand(new_packet['generic_ledger']==dict(domain='r>=1 with inherited canonical fixed recipe; A=prefix101, B=prefix1110 with at least5 bits, C=prefix10011 of m=8+2r',certificate='(200+30r+gM-A-B-C)M+(463+41r+gA-B)A',polynomial='(223+30r+gM-A-B-C)M+(508+41r+gA-B)A',operations='731+71r+gM+gA-A-2B-C',native_scale_products='4-C',witnesses='96+6r',equations=23,fixed_roles='6+15r',geometric_cost=old_packet['generic_ledger']['geometric_cost']),'complete generic declaration')

reports=[]
for before,after in zip(old_packet['examples'],new_packet['examples']):
    r=after['r'];aliases=maps[r];old=before['source'];new=after['source']
    pos0={row[0]:i for i,row in enumerate(old)};pos1={row[0]:i for i,row in enumerate(new)}
    demand(len(pos0)==len(old) and len(pos1)==len(new),'unique computed labels')
    for gone,target in aliases.items():
        demand(old[pos0[gone]]==removed_definitions[gone] and old[pos0[target]]==target_definitions[target],'exact removed and earlier target records')
        demand(pos0[target]<pos0[gone] and target in pos1 and gone not in pos1,'alias availability and deletion')
        demand(new[pos1[target]]==old[pos0[target]],'target retained literally')
    expected=[];removed=[];literal=[];rewritten=[];fanout={name:[] for name in aliases}
    for record in old:
        if record[0] in aliases:
            removed.append(record);continue
        wanted=list(record)
        for slot in (2,3):
            name=record[slot]
            if type(name) is str and name in aliases:
                wanted[slot]=aliases[name]
                fanout[name].append(dict(consumer=record[0],operand_index=slot,target=aliases[name]))
        expected.append(wanted)
        if wanted==record:literal.append(record[0])
        else:rewritten.append(dict(before=record,after=wanted))
    demand(new==expected,'all successor rows and order')
    expected_fans={}
    if r in (1,4):
        expected_fans['left_support_P4']=[f'left_form_high_shift_{j}' for j in range(r-1,-1,-1)]
        expected_fans['left_pair_factor_2']=[f'left_form_repeated_{j}' for j in range(r-1,-1,-1)]
        if r==1:expected_fans['left_support_P5']=['left_short_history_correction']
    else:
        expected_fans={'left_support_P12':['left_six_high_shift_b','left_six_high_shift_a','native_shared_P19'],'left_pair_factor_6':['left_six_repeated_b','left_six_repeated_a']}
    for name,users in expected_fans.items():
        demand(fanout[name]==[dict(consumer=x,operand_index=2,target=aliases[name]) for x in users],'complete exact alias fanout')
    demand((len(literal),len(rewritten),len(removed))=={1:(806,3,3),2:(871,5,2),4:(1016,8,2)}[r],'disjoint record partition')
    # Compare every inherited field; the exact changed-field set is explicit.
    altered={'source','stages','ports','certificate_ledger','certificate_prefix_rows','polynomial_ledger','static_checks','native_scale_products','form_decoder_splice','pack_power_alias_splice'}
    demand(set(after)==set(before)-{'form_decoder_splice'}|{'pack_power_alias_splice'},'example schema')
    for name in set(before)-altered:demand(after[name]==before[name],'inherited field '+name)
    wanted_ports=dict(before['ports'])
    if r==2:wanted_ports['left_support_P12']='geom_P12'
    demand(after['ports']==wanted_ports,'all computed ports and only P12 change')
    demand(after['native_scale_products']==4,'native product count in actual non-C examples')
    partitions=[]
    for graph in (before,after):
        start=0;blocks={}
        for stage,declared in graph['stages'].items():
            block=graph['source'][start:start+declared['operations']];start+=len(block)
            demand(census(block)==declared,'actual stage census')
            blocks[stage]=block
        demand(start==len(graph['source']),'whole stage coverage');partitions.append(blocks)
    blocks0,blocks1=partitions
    demand(list(blocks0)==list(blocks1),'stage order unchanged')
    for stage,block in blocks0.items():
        expected_block=[]
        for record in block:
            if record[0] not in aliases:
                expected_block.append(record[:2]+[aliases.get(x,x) if type(x) is str else x for x in record[2:]])
        demand(blocks1[stage]==expected_block,'all stage record boundaries')
    supplied=after['ordinary_parameters']+after['positive_auxiliaries'];initial=set(supplied)
    demand(len(initial)==len(supplied) and not initial.intersection(pos1),'supplied uniqueness')
    edges={};occurrences=defaultdict(list)
    for index,(name,op,left,right) in enumerate(new):
        demand(op in ('*','+','-') and type(name) is str,'row type')
        edges[name]=[]
        for slot,arg in enumerate((left,right),2):
            if type(arg) is str:
                demand(arg in initial or (arg in pos1 and pos1[arg]<index),'topological binding')
                demand(arg not in aliases,'retired operand gone');edges[name].append(arg)
            elif type(arg) is dict:
                demand(set(arg)=={'fixed'} and type(arg['fixed']) is str,'fixed role schema')
                occurrences[arg['fixed']].append(dict(consumer=name,operator=op,operand_index=slot))
            else:demand(type(arg) is int,'integer literal')
    live=set();pending=[after['output']]
    while pending:
        x=pending.pop()
        if x not in live:live.add(x);pending.extend(edges.get(x,[]))
    demand(set(pos1)|initial<=live,'all computed and supplied values live')
    demand(set(occurrences)==set(before['static_checks']['named_fixed_roles']) and len(occurrences)==6+15*r,'fixed role identity')
    demand(all(len(x)==1 for x in occurrences.values()),'one occurrence per fixed role')
    demand({k:v for k,v in occurrences.items() if v[0]['operator']!='*'}=={'gamma':[dict(consumer='program_tau',operator='+',operand_index=3)]},'retained gamma exception')
    demand(after['static_checks']==dict(topology=True,all_computed_live=True,all_supplied_live=True,named_fixed_roles=sorted(occurrences)),'independent static flags')
    def references(v):
        if type(v) is str:demand(v in initial or v in pos1,'computed descriptor binding')
        elif type(v) is list:
            for q in v:references(q)
        elif type(v) is dict:
            for q in v.values():references(q)
        else:demand(type(v) is int,'descriptor literal')
    for field in ('ports','centered_input_forms','selected_center_ports','lanes_in_order','comparisons'):references(after[field])
    demand(after['ordinary_parameters']==['x'] and len(after['positive_auxiliaries'])==after['witnesses']==96+6*r,'input/witness shape')
    demand(sum(x.startswith('pell_') for x in supplied)==21,'native positive auxiliaries')
    demand(len(after['lanes_in_order'])==after['ell']==62+6*r and after['m']==8+2*r,'lane scale shape')
    demand(blocks1['complete_native64']==blocks0['complete_native64'] and census(blocks1['complete_native64'])==dict(M=33,A=31,operations=64),'native64 literal')
    demand(after['ports']['T']=='native_shared_scale' and new[pos1['pell_q']]==['pell_q','*',16,'native_shared_scale'],'native T consumer')
    demand(len(after['comparisons'])==after['equations']==23 and after['comparisons']==before['comparisons'],'comparison count/binding')
    demand(new[-68:]==old[-68:]==blocks1['single_polynomial_finalizer'] and census(new[-68:])==dict(M=23,A=45,operations=68),'whole literal finalizer')
    demand(after['output']=='comparison_sum_22' and after['ports']['terminal']==['F_1','F_2','F_3','F_4','F_5','F_6','F_1'],'output and endpoint alias')
    demand(after['certificate_prefix_rows']==len(new)-68 and after['certificate_ledger']==census(new[:-68]) and after['polynomial_ledger']==census(new),'complete ledger')
    demand((census(new)['M'],census(new)['A'])=={1:(257,552),2:(285,591),4:(349,675)}[r],'independent full count target')
    demand(census(removed)==dict(M=2 if r==1 else 1,A=1,operations=3 if r==1 else 2),'paid deletion count')
    changed={} if r!=2 else {'left_support_P12':dict(before='left_support_P12',after='geom_P12')}
    expected_splice=dict(aliases=aliases,indicators=dict(A=int(r==1),B=0,C=0),removed_rows=removed,existing_target_records=[old[pos0[x]] for x in aliases.values()],literal_retained_row_names=literal,rebound_rows=rewritten,old_source_digest=digest(old),new_source_digest=digest(new),removed_digest=digest(removed),changed_ports=changed,added_arithmetic_rows=0,removed_ledger=census(removed),fixed_roles_literal_equal=True,positive_auxiliaries_literal_equal=True,comparisons_literal_equal=True,finalizer_literal_equal=True,general_unemitted_cases='No complete seed7/B/C parent examples exist in this input; their all-r grammar is proved separately, not claimed as saved-row coverage.')
    demand(after['pack_power_alias_splice']==expected_splice,'entire author splice metadata')
    reports.append(dict(r=r,m=after['m'],full_rows=len(new),literal_rows=len(literal),rebound_rows=rewritten,removed_rows=removed,aliases=aliases,target_records=[target_definitions[t] for t in aliases.values()],complete_old_fanout=fanout,changed_ports=changed,source_digest=digest(new),stages=after['stages'],certificate_ledger=census(new[:-68]),polynomial_ledger=census(new),positive_witnesses=after['witnesses'],fixed_role_uses=dict(occurrences),all_rows_fields_live=True))
demand(sum(x['full_rows'] for x in reports)==2709,'total covered rows')
result=dict(status='FROZEN first independent inert-record audit PASS; never replay',auditor_sha256=sha(Path(__file__).read_bytes()),inputs=pins,coverage=dict(full_rows=2709,literal_rows=2693,rebound_rows=16,deleted_parent_rows=7,new_arithmetic_rows=0),examples=reports,whole_recipe_literal_equal=True,r0_fallback_literal_equal=True,unemitted_scope='No seed7/B/C saved parent is invented or evaluated; all-r branch/fanout proof is handwritten and separately reviewed.',execution_scope='Fresh record-only comparisons and hashes, operation/role counts, topology/fanout/liveness, stage/metadata/port/native/finalizer checks. No stored instruction/coefficient evaluation, symbolic execution, degree propagation, saved-helper import/replay or build.')
RECEIPT.write_text(json.dumps(result,indent=2)+'\n')
print('PASS: 2709 successor rows =2693 literal +16 rebound; 7 deleted, 0 new; 809/876/1024. Freeze original auditor and first receipt.')
