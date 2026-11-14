#!/usr/bin/env python3
"""Construct the 158-node source factorization; this does not construct a TM.

Usage: python build_essential.py UPSTREAM_DIRECTORY OUTPUT_DIRECTORY
"""
from hashlib import sha256
import json
from pathlib import Path
import sys
from prepare_graph import PINS,source_rows
from compare_sources import graph,require

def nodes(root):
    seen=set();todo=[root]
    while todo:
        t=todo.pop()
        if t in seen:continue
        seen.add(t)
        if t[0]=='node':todo.extend(t[1:])
    return seen

def main():
    upstream,out=map(Path,sys.argv[1:]);out.mkdir(parents=True,exist_ok=True)
    raw=(upstream/'PA196/Program.lean').read_bytes()
    require(sha256(raw).hexdigest()==PINS['PA196/Program.lean'],'wrong source')
    original=raw.decode();changed=original
    edits=[
     ('def node75 : Tree := .node node74 node65',
      'def node75 : Tree := .node (.node node32 node53) (.node node55 node65)'),
     ('def x37 : Tree := .node node55 x36',
      'def x37 : Tree := .node (.node node55 node65) (.node (.node x27 x19) x35)')]
    for before,after in edits:
        require(changed.count(before)==1,'nonunique edit')
        changed=changed.replace(before,after)
    oldrows=source_rows(original);newrows=source_rows(changed)
    require(graph(oldrows)==graph(newrows),'full source CFG changed')
    oldtree,olddefs=source_rows(original,True);newtree,newdefs=source_rows(changed,True)
    oldnodes=nodes(oldtree);newnodes=nodes(newtree)
    def hshape(t,defs):
        return (t[0]=='node' and t[1][0]=='node' and t[2][0]=='node'
                and t[1][1]==defs['node32'] and t[2][1]==defs['node17'])
    oldh=[t for t in oldnodes if hshape(t,olddefs)]
    newh=[t for t in newnodes if hshape(t,newdefs)]
    for row in newrows:
        if row[1]=='CH':row[2]=None
    (out/'essential.sites.json').write_text(json.dumps(newrows,separators=(',',':'))+'\n')
    # The source listing intentionally contains definitions only, no transported theorems.
    listing=changed.split('def sites : Array Site :=')[0]
    listing=listing.replace('namespace PA196.Program','namespace PA196Research.EssentialProgram')
    listing=listing.replace('The 159-node DAG stored in the supplied PA196 machine metadata.',
                            'Experimental 158-node source DAG. No physical TM is asserted.')
    listing+='end PA196Research.EssentialProgram\n'
    (out/'EssentialProgram.lean').write_text(listing)
    receipt={'original_internal_nodes':sum(t[0]=='node' for t in oldnodes),
       'new_internal_nodes':sum(t[0]=='node' for t in newnodes),'leaf_count':len(newrows),
       'full_ordinal_cfg_equal':True,'first_50_paths_unchanged':all(a[0]==b[0] for a,b in zip(oldrows[:50],newrows[:50])),
       'different_paths':sum(a[0]!=b[0] for a,b in zip(oldrows,newrows)),
       'maximum_path_length':max(len(r[0]) for r in newrows),
       'maximum_zero_run':max(max(map(len,r[0].split('1'))) for r in newrows),
       'seed_path':newrows[25][0],
       'original_104_105_helper_shape_count':len(oldh),'new_104_105_helper_shape_count':len(newh),
       'logical_register_seed':[2,0,0,0,0,0,0,0,0],
       'source_sha256':sha256(raw).hexdigest(),
       'limitations':['No binary transition table is produced.',
          'An eight-zero source run exceeds the unchanged origin-scanner interface.',
          'The former decoder helper node75 no longer has the required zero grandchildren.',
          'No PA consistency biconditional or new state-count record follows.']}
    require(receipt['new_internal_nodes']==158,'unexpected DAG count')
    (out/'essential_receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
