#!/usr/bin/env python3
"""Compare two U208 source CFGs using subtree ordinal intervals.

Usage: python compare_sources.py ARCHIVE_DIRECTORY OUTPUT_DIRECTORY
"""
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import sys
from zipfile import ZipFile

SOURCES = [
 ('U208_ConPA_2026-10-29.zip', 'U208_ConPA_2026-10-29/machine/sites.json'),
 ('u208_research_2026-10-29.zip', 'u208_research_2026-10-29/machine/u208.sites.json')]

def require(condition, message):
    if not condition: raise ValueError(message)

def graph(rows):
    intervals = {}
    for i, (path, op, arg) in enumerate(rows):
        for k in range(len(path)+1):
            prefix=path[:k]
            if prefix in intervals: intervals[prefix][1]=i
            else: intervals[prefix]=[i,i]
    leaves={r[0] for r in rows}
    require(len(leaves)==len(rows), 'duplicate leaf')
    for prefix in intervals:
        if prefix in leaves:
            require(prefix+'0' not in intervals and prefix+'1' not in intervals, 'non-prefix-free paths')
        else:
            require(prefix+'0' in intervals and prefix+'1' in intervals, 'nonbinary trie')
    require([r[0] for r in rows]==sorted(leaves),'leaf order differs')
    def next_pc(i): return i if i < len(rows) else None
    def cut(path, bit, n):
        positions=[i for i,x in enumerate(path) if x==bit]
        require(n > 0 and len(positions)>=n, 'invalid jump depth')
        return path[:positions[-n]]
    cfg=[]
    for i,(path,op,arg) in enumerate(rows):
        if op=='CI': cfg.append(['inc',arg,next_pc(i+1)])
        elif op=='CD': cfg.append(['dec',arg,next_pc(intervals[cut(path,'0',1)][1]+1),next_pc(i+1)])
        elif op=='CB': cfg.append(['jump',next_pc(intervals[cut(path,'0',arg)][1]+1)])
        elif op=='CC': cfg.append(['jump',intervals[cut(path,'1',arg)][0]])
        elif op=='CH': cfg.append(['halt'])
        else: raise ValueError(op)
    return cfg

def main():
    source, dest=map(Path,sys.argv[1:]);dest.mkdir(parents=True,exist_ok=True)
    graphs=[];rows_all=[];entries=[]
    for index,(archive,member) in enumerate(SOURCES):
        with ZipFile(source/archive) as z:data=z.read(member)
        rows=json.loads(data);g=graph(rows);graphs.append(g);rows_all.append(rows)
        (dest/f'class{index}.sites.json').write_bytes(data)
        entries.append({'archive':archive,'member':member,'sha256':sha256(data).hexdigest(),
          'leaf_count':len(rows),'operation_counts':dict(Counter(r[1] for r in rows)),
          'max_path':max(len(r[0]) for r in rows),
          'max_zero_run':max(max(map(len,r[0].split('1'))) for r in rows),
          'cfg_sha256':sha256(json.dumps(g,separators=(',',':')).encode()).hexdigest()})
    require(graphs[0]==graphs[1],'source CFGs differ')
    require([r[1:] for r in rows_all[0]]==[r[1:] for r in rows_all[1]],'ordered leaf words differ')
    result={'entries':entries,'same_ordered_operations':True,'same_ordinal_cfg':True,
     'different_paths':sum(a[0]!=b[0] for a,b in zip(*rows_all)),
     'nonhalt_edges':sum(len(r)-2 if r[0] in ('inc','dec') else int(r[0]=='jump') for r in graphs[0]),
     'limitations':['This resolves the program graph but does not verify a changed physical interpreter.']}
    (dest/'source_comparison.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
