#!/usr/bin/env python3
"""Compare four grafts to every literal196 table, without assuming old starts.

Usage: python3 check_all_prior_graphs.py PROVEIT_DOCS_INCOMING INVENTORY_JSON
The inventory was independently produced by audit_archives.py. All listed
196-state tables in this snapshot are in the top-level archives.
"""
from collections import Counter
from pathlib import Path
import json
import sys
import zipfile
import verify_grafts as v

def parse(text):
    rows={}
    for line in text.splitlines():
        line=line.split('#')[0].strip()
        if not line:continue
        q,b,w,d,t=line.split()
        q,b,w,t=map(int,(q,b,w,t))
        v.require((q,b)not in rows and b in(0,1)and w in(0,1)and d in('L','R'),'malformed prior row')
        rows[q,b]=(w,d,t)
    qs={q for q,b in rows}
    v.require(len(qs)==196 and set(rows)=={(q,b)for q in qs for b in(0,1)},'not a complete196table')
    return rows

def outputs(rows):
    return Counter(tuple(rows[q,b][:2] for b in(0,1))for q in {q for q,b in rows})

def main():
    incoming=Path(sys.argv[1])
    inv=json.loads(Path(sys.argv[2]).read_text())
    target=[]
    for label in('candidate_0','candidate_1','zerojump_0','zerojump_1'):
        rows=v.read_machine(v.INP/(label+'_machine.tm'))
        target.append((label,v.canonical(rows,0)[0],outputs(rows)))
    archive_hashes={e['first_location']:e['sha256'] for e in inv['archives'] if e['depth']==0}
    archive_cache={}
    seen=set()
    examined=0
    rooted_trials=0
    matches=[]
    prior_records=[]
    for e in inv['tables']:
        if e['states']!=196 or e['parsed_sha256'] in seen:continue
        seen.add(e['parsed_sha256'])
        v.require('!'not in e['archive'],'unexpected nested196archive')
        if e['archive']not in archive_cache:
            data=(incoming/e['archive']).read_bytes()
            v.require(v.digest(data)==archive_hashes[e['archive']],'changed archive bytes')
            archive_cache[e['archive']]=zipfile.ZipFile(incoming/e['archive'])
        data=archive_cache[e['archive']].read(e['member'])
        v.require(v.digest(data)==e['sha256'],'changed prior table bytes')
        rows=parse(data.decode('utf-8-sig'))
        oldoutputs=outputs(rows)
        possible={h:label for label,h,signature in target if signature==oldoutputs}
        tried=0
        if possible:
            for q in sorted({q for q,b in rows}):
                tried+=1
                h,n=v.canonical(rows,q)
                if h in possible:
                    matches.append({'candidate':possible[h],'archive':e['archive'],'member':e['member'],'prior_start':q})
        rooted_trials+=tried
        examined+=1
        prior_records.append({'archive':e['archive'],'member':e['member'],'sha256':e['sha256'],
                              'parsed_sha256':e['parsed_sha256'],'possible_after_action_signature_filter':len(possible),
                              'roots_tried':tried})
    for z in archive_cache.values():z.close()
    v.require(examined==127,'prior distinct-table count differs')
    v.require(not matches,'a graft is an already supplied graph')
    print(json.dumps({'status':'PASS','prior_occurrences':268,'parsed_distinct_prior196_tables':examined,
                     'arbitrary_root_canonicalizations':rooted_trials,'candidates':4,'matches':matches,
                     'scope':'No graft is isomorphic to any supplied literal196-state table at any choice of its initial control, preserving read/write/move actions and halting.',
                     'prior_tables':prior_records},indent=2))

if __name__=='__main__':main()
