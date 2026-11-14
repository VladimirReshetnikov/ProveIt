#!/usr/bin/env python3
"""Exact blank-tape replay of the two designated rejected196 controls."""
from pathlib import Path
import json,sys
from inventory import parse_table,digest

def main():
    p=Path(sys.argv[1]);manifest=json.loads((p/'catalogue.json').read_text());result=[]
    for m in manifest['tables']:
        if m['status']!='rejected':continue
        raw=(p/(m['name']+'.tm')).read_bytes()
        if digest(raw)!=m['sha256']:raise ValueError('changed table')
        meta,t=parse_table(raw);states={q for q,b in t}
        q=m['start'];head=0;ones=set();steps=0;visited=set()
        while q in states and steps<100000:
            bit=int(head in ones);write,move,target=t[q,bit];visited.add((q,bit))
            if write:ones.add(head)
            else:ones.discard(head)
            head+=1 if move=='R' else -1;q=target;steps+=1
        if q!=m['halt'] or steps!=43563:raise ValueError('unexpected blank-run outcome')
        result.append({'name':m['name'],'sha256':m['sha256'],'halted':True,'transitions':steps,'final_state':q,'final_head':head,'final_ones':sorted(ones),'final_ones_sha256':digest(json.dumps(sorted(ones),separators=(',',':')).encode()),'row_115_1_visited':(115,1) in visited})
    (p/'rejected_blank_halt_replay.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps([{k:v for k,v in r.items() if k!='final_ones'} for r in result],indent=2))

if __name__=='__main__':main()
