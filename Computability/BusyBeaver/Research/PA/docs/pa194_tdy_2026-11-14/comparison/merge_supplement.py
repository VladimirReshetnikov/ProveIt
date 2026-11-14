#!/usr/bin/env python3
"""Merge normalized JSON literal tables into the frozen numeric-table census."""
import collections,csv,hashlib,json,pathlib
from inventory import parse,canonical,digest,write_csv
p=pathlib.Path(__file__).resolve().parent
corpus=json.loads((p/'corpus_tables.json').read_text());byhash={r['sha256']:r for r in corpus}
records=json.loads((p/'literal_tables.json').read_text());meta={r['sha256']:r for r in records}
summary=json.loads((p/'census_summary.json').read_text())
candidate=parse((p.parent/'artifacts/pa194_tdy.tm').read_bytes());ck=canonical(candidate,True,True)
for r in json.loads((p/'json_table_supplement.json').read_text()):
    h=r['sha256'];data=r['text'].encode();assert digest(data)==h
    if h in byhash:
        new=[x for x in r['paths'] if x not in byhash[h]['paths']]
        byhash[h]['paths'].extend(new);meta[h]['paths'].extend(new);meta[h]['occurrences']+=len(new);continue
    m=parse(data);assert m is not None;key=canonical(m)
    if len(m[1])==194 and key is not None and canonical(m,True,True)==ck:summary['candidate_matches'].extend(r['paths'])
    rec={'sha256':h,'states':len(m[1]),'transition_rows':len(m[0]),'spanning_root':key is not None,
         'external_targets':sorted({target for _,_,target in m[0].values()}-m[1]),
         'external_target_count':len({target for _,_,target in m[0].values()}-m[1]),
         'start':m[2],'start_status':'JSON normalization; dense convention only' if m[2] is not None else 'unknown',
         'canonical_sha256':digest(key.encode()) if key is not None else None,'occurrences':len(r['paths']),
         'paths':r['paths'],'sample_path':r['paths'][0]}
    records.append(rec);meta[h]=rec;byhash[h]={'sha256':h,'text':r['text'],'paths':r['paths']};corpus.append(byhash[h])
groups=collections.defaultdict(list)
for r in records:groups[r['canonical_sha256'] or 'disconnected:'+r['sha256']].append(r)
classes=[]
for k,rs in groups.items():
    rep=rs[0];classes.append({**{k:v for k,v in rep.items() if k not in ('occurrences','paths')},
        'external_target_counts':sorted(set(r['external_target_count'] for r in rs)),
        'byte_forms':len(rs),'occurrences':sum(r['occurrences'] for r in rs),'paths':sorted(set(p for r in rs for p in r['paths']))})
classes.sort(key=lambda r:(r['states'],r['canonical_sha256'] or r['sha256']))
summary['counts'].update(recognized_table_occurrences=sum(len(r['paths']) for r in corpus),distinct_table_bytes=len(corpus),spanning_table_classes=sum(r['spanning_root'] for r in classes),disconnected_byte_forms=sum(not r['spanning_root'] for r in classes))
summary['spanning_classes_by_states']=dict(sorted(collections.Counter(r['states'] for r in classes if r['spanning_root']).items()))
summary['terminal_count_by_byte_forms']=dict(sorted(collections.Counter(r['external_target_count'] for r in records).items()))
summary['json_supplement']=json.loads((p/'json_table_supplement.receipt.json').read_text())
summary['json_supplement'].pop('source_files',None)
summary['scope']='All 535 filed catalogue representatives; all 14 direct PA .tm files; all 11 incoming ZIPs; all six retained historical filed ZIPs, recursively expanded with byte-identical archives deduplicated; normalized literal JSON tables from all incoming and historical ZIPs plus the 21 repository JSON files identified by the inherited JSON census. Complete numeric five-column binary tables are recognized in .tm/.txt/.tsv/.csv. No arbitrary generators are executed. Unknown code-only designs are not certified or silently treated as absent. Source paths and exact frozen table bytes are included. Class labels record structure; no consistency theorem follows from this census.'
for fn,obj in [('literal_tables.json',records),('literal_classes.json',classes),('census_summary.json',summary)]:
    (p/fn).write_text(json.dumps(obj,indent=2)+'\n')
(p/'corpus_tables.json').write_text(json.dumps(corpus,separators=(',',':'))+'\n')
write_csv(p/'literal_classes.csv',classes,['states','canonical_sha256','spanning_root','byte_forms','occurrences','start','start_status','sample_path'])
print(json.dumps(summary,indent=2))
