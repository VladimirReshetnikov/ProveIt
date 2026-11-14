#!/usr/bin/env python3
"""Recover complete textual and five-column-array tables embedded in JSON.

This does not interpret programs, proof receipts, transition dictionaries or
arbitrary machine encodings. It adds an explicit recoverable JSON supplement
to the separate literal-file census.
"""
import hashlib,json,subprocess
from pathlib import Path
import current_census as c

ROOT=Path(__file__).resolve().parent
def candidates(value,pointer='$'):
    if isinstance(value,str):
        if '\n' in value and len(value)>30:
            try:data=value.encode('ascii')
            except UnicodeEncodeError:return
            if c.parse_table(data) is not None:yield pointer,data
    elif isinstance(value,list):
        if len(value)>=2 and all(isinstance(x,list) and len(x)==5 and isinstance(x[0],int) and x[1] in (0,1) and x[2] in (0,1) and x[3] in ('L','R') and isinstance(x[4],int) for x in value):
            data=('\n'.join(' '.join(map(str,x)) for x in value)+'\n').encode()
            if c.parse_table(data) is not None:yield pointer,data
        else:
            for i,x in enumerate(value):yield from candidates(x,pointer+'/'+str(i))
    elif isinstance(value,dict):
        for k,x in value.items():yield from candidates(x,pointer+'/'+str(k))

def main():
    old=json.loads((ROOT/'current_frontier194.json').read_text()); groups={tuple(x['canonical']):x for x in old}
    paths=subprocess.check_output(['rg','--files','-g','*.json','ProveIt/Computability/BusyBeaver/Research/PA','inventory_work/incoming'],cwd=ROOT.parent).decode().splitlines()
    found=[];failures=[];new=[];cache={}
    for name in paths:
        p=ROOT.parent/name
        try:v=json.loads(p.read_text())
        except (UnicodeError,json.JSONDecodeError) as e:
            failures.append({'path':name,'error':repr(e)});continue
        for pointer,data in candidates(v):
            table=c.parse_table(data); rows,states,start,halt=table
            digest=hashlib.sha256(data).hexdigest()
            if name.startswith('ProveIt/'):
                source_name=name[len('ProveIt/'):]
            else:
                rel=Path(name).relative_to('inventory_work/incoming')
                source_name='docs/incoming/'+rel.parts[0]+'.zip::'+'/'.join(rel.parts[1:])
            locator=source_name+'::JSON'+pointer
            item={'locator':locator,'sha256':digest,'states':len(states)}
            if len(states)==194:
                if digest not in cache:cache[digest]=c.canonical(rows,states)[0]
                key=cache[digest]; item['whole_graph_sha256']=c.graph_digest(key)
                if key is not None:
                    if key not in groups:
                        groups[key]={'whole_graph_sha256':c.graph_digest(key),'states':194,'byte_sha256':[],'locators':[],'canonical':list(key)}
                        new.append(item.copy())
                    g=groups[key]
                    if digest not in g['byte_sha256']:g['byte_sha256'].append(digest)
                    if locator not in g['locators']:g['locators'].append(locator)
            found.append(item)
    result={'scope':'All JSON string values containing a complete numeric five-column binary L/R table, and arrays of such five-column rows, in the pinned PA tree and extracted incoming archives. Does not interpret arbitrary code or alternate JSON transition encodings.','JSON_files_examined':len(paths),'recovered_table_occurrences':len(found),'new_194_graphs':new,'combined_194_graph_classes':len(groups),'parse_failures':failures,'tables':found}
    (ROOT/'json_supplement.json').write_text(json.dumps(result,indent=2)+'\n')
    (ROOT/'combined_frontier194.json').write_text(json.dumps(list(groups.values()),indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='tables'},indent=2))

if __name__=='__main__':main()
