#!/usr/bin/env python3
"""Join census records into class and manuscript-comparison indexes."""
from pathlib import Path
import collections,csv,json

def main():
    base=Path(__file__).resolve().parent;p=base/'census'
    graphs=json.loads((p/'root_free_graphs.json').read_text());tables=json.loads((p/'tables.json').read_text())
    by_transition={x['transition_sha256']:x['root_free_graph_sha256'] for x in graphs}
    grouped=collections.defaultdict(list);designated=collections.defaultdict(list)
    for x in tables:
        if x['transition_sha256'] in by_transition:grouped[by_transition[x['transition_sha256']]].append(x)
    for label in ('designated196','designated208'):
        for x in json.loads((p/label/'catalogue.json').read_text())['tables']:
            designated[by_transition[x['transition_sha256']]].append({k:x[k] for k in ('name','status','start','halt')})
    result=[]
    for h,items in grouped.items():
        result.append({'graph_sha256':h,'working_states':items[0]['working_states'],'table_occurrences':len(items),'raw_sha256s':sorted({x['raw_sha256'] for x in items}),'transition_sha256s':sorted({x['transition_sha256'] for x in items}),'designated_members':designated.get(h,[]),'sources':[{k:x[k] for k in ('source','member')} for x in items]})
    result.sort(key=lambda x:(x['working_states'],not bool(x['designated_members']),x['graph_sha256']))
    (p/'graph_classes.json').write_text(json.dumps(result,indent=2)+'\n')
    (p/'rejected195_graphs.json').write_text(json.dumps([x for x in result if x['working_states']==195],indent=2)+'\n')
    with (p/'graph_classes.csv').open('w',newline='') as f:
        fields=['graph_sha256','working_states','table_occurrences','designated_members','first_source','first_member'];w=csv.DictWriter(f,fields);w.writeheader()
        for x in result:w.writerow({'graph_sha256':x['graph_sha256'],'working_states':x['working_states'],'table_occurrences':x['table_occurrences'],'designated_members':'; '.join(y['name']+':'+y['status'] for y in x['designated_members']),'first_source':x['sources'][0]['source'],'first_member':x['sources'][0]['member']})
    payloads={x['sha256']:x for x in json.loads((p/'archives.json').read_text())}
    archives={Path(x['location']).name:payloads[x['sha256']] for x in json.loads((p/'archive_occurrences.json').read_text()) if x['depth']==0}
    section=(base/'COMPARISON.md').read_text().split('## All 27 incoming archives',1)[1].split('## The 23 designated',1)[0]
    matrix=[]
    for line in section.splitlines():
        if not line.startswith('| `'):continue
        name,contribution,limitation=[x.strip() for x in line.split('|')[1:-1]];name=name.strip('`');a=archives[name]
        matrix.append({'archive':name,'sha256':a['sha256'],'bytes':a['bytes'],'direct_table_members':a['tm_members'],'contribution':contribution,'limitation':limitation})
    if len(matrix)!=27:raise ValueError('comparison matrix should cover all 27 archives')
    (p/'archive_comparison.json').write_text(json.dumps(matrix,indent=2)+'\n')
    with (p/'archive_comparison.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(matrix[0]));w.writeheader();w.writerows(matrix)
    print(json.dumps({'graph_classes':len(result),'archive_comparison_rows':len(matrix)},indent=2))

if __name__=='__main__':main()
