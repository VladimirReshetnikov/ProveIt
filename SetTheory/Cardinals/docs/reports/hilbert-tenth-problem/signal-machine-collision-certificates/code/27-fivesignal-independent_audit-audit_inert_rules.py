"""Static audit of inert rule data against independently specified finite templates.
No rule dispatch, event-time calculation, physical state or trajectory execution.
"""
import json, hashlib, collections
from fractions import Fraction as F
from pathlib import Path
OUT=Path(__file__).parent; SRC=OUT/'inert_sources'/'RULES.json'
p=json.loads(SRC.read_text()); rules=p['explicit_rules']; meta=p['meta_signals']
speeds={m['name']:F(m['speed']) for m in meta}
assert len(speeds)==len(meta)==169
assert len(rules)==138
assert set(speeds.values())==set(map(F,['0','1','-1','-1/9','1/11','-1/4','2/17','-1/3']))
# Explicit independently written expected phase names, bounds and physical identities.
# Entries: phase, first event, target, anchor, physical outgoing-base direction,
# target speed, collision identity word, outgoing messenger speed word.
phases=[
('L01',0,'X','L',1,'-1/9','XLXL',[-1,1,-1,1]),
('H02',4,'X','L',1,'-1/9','XYXL',[1,-1,-1,1]),
('L03',8,'X','L',1,'1/11','XLXL',[-1,1,-1,1]),
('H04',12,'X','L',1,'1/11','XYDYXL',[1,1,-1,-1,-1,1]),
('L05',18,'X','L',1,'-1/9','XLXL',[-1,1,-1,1]),
('H06',22,'X','L',1,'-1/9','XYXL',[1,-1,-1,1]),
('L07',26,'X','L',1,'1/11','XLXL',[-1,1,-1,1]),
('H08',30,'X','L',1,'1/11','XYDYXL',[1,1,-1,-1,-1,1]),
('transfer_right',36,None,None,1,None,'XYD',[1,1,-1]),
('L09',39,'Y','D',-1,'-1/4','YDYD',[1,-1,1,-1]),
('H10',43,'Y','D',-1,'-1/4','YXYD',[-1,1,1,-1]),
('L11',47,'Y','D',-1,'2/17','YDYD',[1,-1,1,-1]),
('H12',51,'Y','D',-1,'2/17','YX LXYD'.replace(' ',''),[-1,-1,1,1,1,-1]),
('L13',57,'Y','D',-1,'-1/4','YDYD',[1,-1,1,-1]),
('H14',61,'Y','D',-1,'-1/4','YXYD',[-1,1,1,-1]),
('L15',65,'Y','D',-1,'2/17','YDYD',[1,-1,1,-1]),
('H16',69,'Y','D',-1,'2/17','YXLXYD',[-1,-1,1,1,1,-1]),
('transfer_left',75,None,None,-1,None,'YXL',[-1,-1,1]),
('L17',78,'X','L',1,'-1/9','XLXL',[-1,1,-1,1]),
('H18',82,'X','L',1,'-1/9','XYXL',[1,-1,-1,1]),
('L19',86,'X','L',1,'1/11','XLXL',[-1,1,-1,1]),
('H20',90,'X','L',1,'1/11','XYDYXL',[1,1,-1,-1,-1,1]),
('L21',96,'X','L',1,'-1/9','XLXL',[-1,1,-1,1]),
('H22',100,'X','L',1,'-1/9','XYXL',[1,-1,-1,1]),
('L23',104,'X','L',1,'1/11','XLXL',[-1,1,-1,1]),
('H24',108,'X','L',1,'1/11','XYDYXL',[1,1,-1,-1,-1,1]),
('L25',114,'X','L',1,'-1/3','XLXL',[-1,1,-1,1]),
('L26',118,'Y','L',1,'-1/3','XYXLXYXL',[1,-1,-1,1,1,-1,-1,1]),
('L27',126,'D','L',1,'-1/3','XYDYXLXYDYXL',[1,1,-1,-1,-1,1,1,1,-1,-1,-1,1]),
]
seen_rules=set(); covered=[]; observed_temp=set(); phase_receipt=[]
for name,start,target,anchor,start_dir,target_speed,word,outs in phases:
    assert len(word)==len(outs)
    chunk=rules[start:start+len(word)]
    assert len(chunk)==len(word)
    target_occ=[j for j,c in enumerate(word) if c==target]
    if target is not None:
        assert len(target_occ)==2
        temp=target+'_'+name; assert speeds[temp]==F(target_speed); observed_temp.add(temp)
    for j,(r,identity,vs) in enumerate(zip(chunk,word,outs)):
        idx=start+j; covered.append(idx)
        assert r['index']==idx and r['primitive']==name
        expected_in=identity+'0'; expected_out=expected_in
        if target is not None and j==target_occ[0]: expected_out=temp
        if target is not None and j==target_occ[1]: expected_in=temp
        assert r['marker_in']==expected_in and r['marker_out']==expected_out
        assert r['input']==[f'Q{idx}',expected_in]
        assert r['output']==[f'Q{(idx+1)%138}',expected_out]
        vin=start_dir if j==0 else outs[j-1]
        assert F(r['messenger_in_speed'])==speeds[r['input'][0]]==vin
        assert F(r['messenger_out_speed'])==speeds[r['output'][0]]==vs
        assert speeds[expected_in]!=vin and speeds[expected_out]!=vs
        key=frozenset(r['input']); assert key not in seen_rules; seen_rules.add(key)
    phase_receipt.append({'phase':name,'first_index':start,'last_index':start+len(word)-1,'marker_word':word,'outgoing_messenger_speeds':outs})
assert covered==list(range(138))
assert len(observed_temp)==27
assert set(speeds)==set(['L0','X0','Y0','D0'])|observed_temp|{f'Q{j}' for j in range(138)}
assert speeds['Q0']==1 and rules[-1]['output']==['Q0','L0']
# Sorted local pairs are the actual speed-forced left-to-right incoming/outgoing order.
# Record all 138; this checks pairwise-distinct local geometry, not trajectories.
lines=['index\tphase\tinput_set\toutput_set\tincoming_left_to_right\toutgoing_left_to_right']
for r in rules:
    ins=sorted(r['input'],key=lambda x:speeds[x],reverse=True)
    outs=sorted(r['output'],key=lambda x:speeds[x])
    fmt=lambda seq: ','.join(f'{x}:{speeds[x]}' for x in seq)
    lines.append('\t'.join([str(r['index']),r['primitive'],fmt(r['input']),fmt(r['output']),fmt(ins),fmt(outs)]))
(OUT/'all_138_local_rule_checks.tsv').write_text('\n'.join(lines)+'\n')
receipt={'source_sha256':hashlib.sha256(SRC.read_bytes()).hexdigest(),'kind':'Inert finite-table structural/template validation; no rule or trajectory execution',
'events_checked':138,'meta_signals':169,'moving_phases':27,'distinct_speeds':sorted(map(str,set(speeds.values()))),
'all_rules_binary':True,'all_inputs_outputs_distinct_speed':True,'all_input_sets_unique':True,'complete_phase_cover':True,
'cyclic_messenger_label_closure':True,'four_stationary_marker_labels_restored_after_every_primitive':True,
'phase_bounds':phase_receipt,'initial_section':p['initial_section']}
(OUT/'inert_rules_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='phase_bounds'},indent=2))
