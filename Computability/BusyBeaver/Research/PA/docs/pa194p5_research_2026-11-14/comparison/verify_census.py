#!/usr/bin/env python3
"""Replay the finite literal-table census from its bundled byte identities.

This offline verifier re-parses all 762 recognized byte forms, regenerates
their spanning graph classes, binds all 548 direct PA .tm paths to the pinned
Git blob hashes, and checks the eight excluded fragment forms. It verifies
the retained census, not the completeness of a new remote repository crawl.
"""
from pathlib import Path
import collections, hashlib, json
from table_tools import parse_table
from verify_novelty import forms

HERE = Path(__file__).resolve().parent
def sha(raw): return hashlib.sha256(raw).hexdigest()
def gitsha(raw): return hashlib.sha1(('blob %d\0' % len(raw)).encode()+raw).hexdigest()

def main():
    census=json.loads((HERE/'census.json').read_text())
    manifest=json.loads((HERE/'pinned_direct_tm_manifest.json').read_text())
    excluded=json.loads((HERE/'unparsed_diagnostics.json').read_text())
    identities={x['sha256']:x for x in census['identities']}
    cache={}; graphs=set(); no_root=[]; checked={}
    for index,(digest,entry) in enumerate(identities.items(),1):
        raw=(HERE/'census_tables'/(digest+'.tm')).read_bytes()
        if sha(raw)!=digest or gitsha(raw)!=entry['git_blob_sha1']:
            raise ValueError('Byte binding failed: '+digest)
        data=parse_table(raw)
        if data is None or len(data[1])!=entry['states'] or data[2]!=entry['halt']:
            raise ValueError('Table parse/count failed: '+digest)
        key=tuple(sorted(data[0].items()))
        if key not in cache:
            value=forms(data)
            cache[key]=None if value is None else sha(repr(value).encode())
        graph=cache[key]
        if graph!=entry['graph_hash']:
            raise ValueError('Graph class failed: '+digest)
        if graph is None:no_root.append(digest)
        else:graphs.add((len(data[1]),graph))
        checked[digest]=raw
        if index%100==0:print('Verified',index,'literal byte identities',flush=True)
    excluded_bytes={}
    for entry in excluded:
        digest=entry['sha256']
        if digest in excluded_bytes:continue
        raw=(HERE/'excluded_literal_fragments'/(digest+'.tm')).read_bytes()
        if sha(raw)!=digest or parse_table(raw) is not None:
            raise ValueError('Excluded diagnostic check failed: '+digest)
        excluded_bytes[digest]=raw
    paths={x['path']:x['sha256'] for x in census['occurrences']}
    paths.update({x['path']:x['sha256'] for x in excluded})
    byte_total=0
    for entry in manifest['files']:
        digest=paths[manifest['prefix']+entry['path']]
        raw=checked.get(digest,excluded_bytes.get(digest))
        if raw is None or gitsha(raw)!=entry['sha'] or len(raw)!=entry['size']:
            raise ValueError('Pinned direct file mismatch: '+entry['path'])
        byte_total+=len(raw)
    for entry in census['occurrences']:
        if entry['sha256'] not in identities:
            raise ValueError('Unbound occurrence: '+entry['path'])
    actual={'current_direct_tm_files':len(manifest['files']),
            'direct_current_bytes':byte_total,
            'literal_occurrences':len(census['occurrences']),
            'literal_byte_identities':len(identities),
            'spanning_graph_classes':len(graphs),
            'unclassified_byte_identities':len(no_root),
            'graphs_by_state_count':dict(sorted(collections.Counter(str(n) for n,g in graphs).items(),key=lambda x:int(x[0])))}
    for k,v in actual.items():
        if v!=census['summary'][k]:raise ValueError('Summary mismatch: '+k)
    result={'status':'PASS','snapshot':census['snapshot'],'verified':actual,
            'excluded_literal_forms':len(excluded_bytes),'excluded_occurrences':len(excluded),
            'limits':'Replays retained literal bytes and pinned direct-file bindings; it does not recrawl GitHub or independently re-expand the original ZIP payloads.'}
    (HERE/'census_replay.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
