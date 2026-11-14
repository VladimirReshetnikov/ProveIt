#!/usr/bin/env python3
"""Exact structural novelty against the frozen 40-class PA194 frontier.

Uses full canonical transition tuples rather than treating a hash mismatch
as proof of graph inequivalence. The finite comparison permits arbitrary
working-state renaming, every graph-spanning root, tape reflection, and
global bit complementation. It is not a test of semantic equivalence.
"""
import argparse,hashlib,json
from pathlib import Path
from current_census import parse_table,canonical,graph_digest

HERE=Path(__file__).resolve().parent
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('machine',type=Path)
    p.add_argument('--frontier',type=Path,default=HERE/'combined_frontier194.json')
    p.add_argument('--output',type=Path)
    a=p.parse_args();data=a.machine.read_bytes();parsed=parse_table(data)
    assert parsed is not None,'Invalid numeric binary table'
    rows,states,start,halting=parsed
    key,roots=canonical(rows,states);assert key is not None,'No spanning graph root'
    old=json.loads(a.frontier.read_text())
    matches=[{k:v for k,v in x.items() if k!='canonical'} for x in old if tuple(x['canonical'])==key]
    r={'machine':str(a.machine),'working_states':len(states),'transition_rows':len(rows),
       'sha256':hashlib.sha256(data).hexdigest(),'start':start,'halt_labels':sorted(halting),
       'spanning_roots':roots,'whole_graph_sha256':graph_digest(key),
       'frontier_classes':len(old),'frontier_sha256':hashlib.sha256(a.frontier.read_bytes()).hexdigest(),
       'matches':matches,'novel_in_recognized_corpus':not matches,
       'scope':'Exact tuples under working-state renaming, any spanning root, reflection and bit complement; literal files plus complete tables embedded in JSON. Not semantic inequivalence or global priority.'}
    text=json.dumps(r,indent=2)+'\n'
    if a.output:a.output.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
