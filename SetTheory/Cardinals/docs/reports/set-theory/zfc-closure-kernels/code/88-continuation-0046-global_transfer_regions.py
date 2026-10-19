#!/usr/bin/env python3
"""Recognize total affine regions directly in the guarded instruction CFG.

Every single-counter loop certificate has a finite, increment-only positive
body that does not increment its counter. Its exit map follows by induction
on that natural counter. This search does not infer a binary compiler or
machine-state saving from an algebraic equality.
"""
from pathlib import Path
import sys
sys.dont_write_bytecode=True
from state_paths import output_directory
from collections import defaultdict,Counter
import json,hashlib

ROOT=Path(__file__).resolve().parents[2]
INPUT=ROOT/'experiments/audit_inputs/quotient.json'
DATA=json.loads(INPUT.read_text())
GRAPH=DATA['graph'];EPS=DATA['epsilon'];SITES=DATA['sites']
ID=tuple(tuple(int(i==j) for j in range(10)) for i in range(10))

def compose(A,B):
    return tuple(tuple(sum(B[i][k]*A[k][j] for k in range(10))
                       for j in range(10)) for i in range(10))

def inc(r):
    M=[list(row) for row in ID];M[r][9]+=1
    return tuple(map(tuple,M))

def control_path(i):
    out=[]
    while GRAPH[i][0][0] in ('B','C'):
        assert i not in out;out.append(i);i=GRAPH[i][1][0]
    assert i==EPS[out[0]] if out else True
    return i,out

def loop(i):
    e,successors=GRAPH[i]
    if e[0]!='D':return
    counter=e[1];j=successors[0];body=[];counts=[0]*9;seen={i}
    while j!=i:
        if j in seen:return
        seen.add(j);body.append(j);op,nxt=GRAPH[j]
        if op[0]=='I':counts[op[1]]+=1
        elif op[0] not in ('B','C'):return
        assert len(nxt)==1;j=nxt[0]
    if counts[counter]:return
    exit,tail=control_path(successors[1])
    M=[list(row) for row in ID];M[counter]=[0]*10
    for k in range(9):
        if k!=counter:M[k][counter]+=counts[k]
    return {'kind':'transfer_loop','entry':i,'exit':exit,'counter':counter,
            'body':body,'exit_control':tail,'increments':counts,
            'map':tuple(map(tuple,M)),'footprint':set([i]+body+tail)}

def main():
    assert __debug__
    macros={};loops=[]
    for i,(e,nxt) in enumerate(GRAPH):
        if e[0]=='I':
            exit,tail=control_path(nxt[0])
            macros[i]={'kind':'increment','entry':i,'exit':exit,'map':inc(e[1]),
                       'footprint':set([i]+tail),'register':e[1]}
        else:
            M=loop(i)
            if M:macros[i]=M;loops.append(M)
    predecessors=defaultdict(set)
    for i,(e,nxt) in enumerate(GRAPH):
        for j in nxt:predecessors[j].add(i)
    def external_entries(footprint):
        return sorted(j for j in footprint if predecessors[j]-footprint)
    redundancies=[];maps=defaultdict(list)
    for start in macros:
        seen=set();chain=[];footprint=set();M=ID;i=start
        for length in range(1,17):
            if i in seen or i not in macros:break
            seen.add(i);block=macros[i];chain.append(i);footprint|=block['footprint']
            N=compose(M,block['map'])
            if N==M:
                redundancies.append({'entry':start,'redundant_macro':i,
                    'prefix_chain':chain[:-1],'redundant_kind':block['kind'],
                    'exit':block['exit'],'external_entries':external_entries(footprint),
                    'prefix_map':M,'redundant_map':block['map']})
            M=N;i=block['exit']
            maps[M].append((start,i,tuple(chain)))
    # Algebraically equal chains with distinct first macro effects suggest
    # alternate segmentation, while suffix copies of the same source text
    # are deliberately not presented as new identities.
    alternatives=[]
    for M,regions in maps.items():
        forms=defaultdict(list)
        for start,exit,chain in regions:
            sig=tuple(macros[x]['map'] for x in chain)
            forms[sig].append((start,exit,chain))
        if len(forms)>1:
            examples=[v[0] for v in forms.values()]
            alternatives.append({'map':M,'distinct_factorizations':len(forms),
                                 'examples':examples})
    serial=[]
    for item in loops:
        obj={k:v for k,v in item.items() if k!='footprint'}
        obj['path']=SITES[item['entry']][0];serial.append(obj)
    report={'status':'PASS','scope':'Exact source-level transfer-loop certificates and affine identities; no changed binary machine or blanket totality claim.',
            'source_hash':hashlib.sha256(INPUT.read_bytes()).hexdigest(),
            'arithmetic_macros':len(macros),'transfer_loop_occurrences':len(loops),
            'distinct_transfer_effects':len({m['map'] for m in loops}),
            'chain_limit':16,'redundancy_witnesses':len(redundancies),
            'single_entry_redundancy_witnesses':sum(x['external_entries'] in ([],[x['entry']]) for x in redundancies),
            'distinct_maps_with_alternate_factorizations':len(alternatives),
            'loops':serial,'redundancies':redundancies,'alternate_factorizations':alternatives}
    output=output_directory()/'global_transfer_regions.json';output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('loops','redundancies','alternate_factorizations')},indent=2))
    for r in redundancies[:15]:print('REDUNDANT',r['entry'],r['redundant_macro'],r['prefix_chain'],r['external_entries'])

if __name__=='__main__':main()
