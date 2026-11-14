#!/usr/bin/env python3
"""Inventory designated 196-state tables without promoting experimental status."""
from pathlib import Path
from collections import defaultdict, deque
import argparse, hashlib, json, zipfile

SELECTED = {
 'conpa_tm_comparison_and_search.zip': [('conpa_tm_study/research196/accepted196_register_swap/pa196_register_AD_swap.tm','AD register swap','uniform symbolic/startup checks reported')],
 'conpa_tm_comparison_and_reduction_search.zip': [
  ('conpa_tm_comparison_and_reduction_search/machines/experimental_mp_result_in_h_196.tm','MP result in H','experimental; bounded frame checks'),
  ('conpa_tm_comparison_and_reduction_search/machines/experimental_mp_without_zero_push_196.tm','MP without zero push','experimental; bounded frame checks'),
  ('conpa_tm_comparison_and_reduction_search/machines/published_pa196.tm','published PA196','upstream Lean endpoint; internal reverse implication separate')],
 'pa_tm_extended_research_2026-11-13.zip': [
  ('pa_tm_extended_research_2026-11-13/auxiliary196/pa196_close_cd%d.tm'%i,'closing CD%d'%i,'constrained symbolic/startup checks reported') for i in [3,4,5,6]],
 'pa_tm_research_2026-11-13.zip': [('pa_tm_research_2026-11-13/alternative196/alternative196.tm','shorter path alternative','uniform symbolic/startup checks reported')],
 'pa_tm_comparison_and_reductions.zip': [
  ('pa_tm_research/rotated196/candidate/data/rotated196.tm','rotated196','uniform symbolic/startup checks reported'),
  ('pa_tm_research/rotated196/candidate-macro62/data/rotated196-macro62.tm','rotated macro62','uniform symbolic/startup checks reported')],
 'pa_consistency_research.zip': [('pa_consistency_research/data/variant196.tm','eight-zero scanner regrouping','uniform symbolic/startup checks reported')],
 'pa_consistency_reduction.zip': [
  ('pa_consistency_reduction/comparison/audit/rebracketed196_dense.tm','rebracketed196','uniform symbolic/startup checks reported'),
  ('pa_consistency_reduction/comparison/audit/h_catalan_node170_3_133_37.tm','H-only Shift','uniform symbolic/startup checks reported')],
}

def parse(raw):
    table={}
    for line in raw.decode().splitlines():
        if not line.strip() or line.lstrip().startswith('#'): continue
        parts=line.split()
        if len(parts)!=5: raise ValueError('malformed row: '+line)
        q,b,w,d,t=parts
        key=int(q),int(b)
        if key in table: raise ValueError('duplicate row')
        value=int(w),d,int(t)
        if key[1] not in [0,1] or value[0] not in [0,1] or d not in ['L','R']:
            raise ValueError('nonbinary row')
        table[key]=value
    return table

def canonical(table):
    states={q for q,_ in table}
    if 0 not in states: raise ValueError('designated literal start is not 0')
    ids={0:0};queue=deque([0]);rows=[]
    while queue:
        q=queue.popleft();row=[]
        for b in [0,1]:
            w,d,t=table[q,b]
            if t not in states: target=-1
            else:
                if t not in ids: ids[t]=len(ids);queue.append(t)
                target=ids[t]
            row.append([w,d,target])
        rows.append(row)
    return rows,ids

def main():
    ap=argparse.ArgumentParser();ap.add_argument('incoming',type=Path);ap.add_argument('output',type=Path)
    args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    (args.output/'tables').mkdir(exist_ok=True)
    items=[];classes=defaultdict(list)
    for archive,entries in SELECTED.items():
        path=args.incoming/archive
        archive_hash=hashlib.sha256(path.read_bytes()).hexdigest()
        with zipfile.ZipFile(path) as z:
            for member,label,status in entries:
                raw=z.read(member);table=parse(raw);states={q for q,_ in table}
                if len(states)!=196 or set(table)!={(q,b)for q in states for b in [0,1]}:
                    raise ValueError('state/row census differs')
                halts={t for _,_,t in table.values()}-states
                if len(halts)!=1: raise ValueError('not one distinct halt label')
                rows,ids=canonical(table)
                if len(ids)!=196: raise ValueError('not all controls graph-reachable')
                encoded=json.dumps(rows,separators=(',',':')).encode()
                graph_hash=hashlib.sha256(encoded).hexdigest()
                ordinal=len(items)+1;filename=f'{ordinal:02d}.tm'
                (args.output/'tables'/filename).write_bytes(raw)
                item={'archive':archive,'archive_sha256':archive_hash,'member':member,'label':label,
                      'reported_status':status,'file':'tables/'+filename,'sha256':hashlib.sha256(raw).hexdigest(),
                      'working_states':196,'rows':392,'graph_reachable':196,'halt_labels':sorted(halts),
                      'canonical_graph_sha256':graph_hash,'old_to_canonical':ids,'canonical_rows':rows}
                classes[graph_hash].append(ordinal);items.append(item)
    report={'scope':'Fourteen designated 196-state tables including two explicitly experimental MP variants. Graph census is not semantic or PA verification.',
            'selected_count':len(items),'rooted_graph_classes':len(classes),'classes':list(classes.values()),'tables':items}
    (args.output/'census.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='tables'},indent=2))

if __name__=='__main__':main()
