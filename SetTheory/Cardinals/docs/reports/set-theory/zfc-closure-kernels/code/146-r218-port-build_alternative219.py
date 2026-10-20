#!/usr/bin/env python3
"""Literal35-row change and exact guarded-source-CFG identity with published219.

The patch has no added/deleted states.  Source transformations are certified by
equal primitive effects and equal targets for both decrement guards, using two
independent target resolvers from the authenticated K221 source implementation.
"""
from pathlib import Path
import argparse,json,sys
from common import *
PARENT_TABLE_SHA='b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26'
PARENT_SOURCE_SHA='0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789'
SOURCE_CODE_SHA='4b355b81373a06ce2d8d99f56ac88afee8bbbd934d21f4f2729d864d9807683f'
BUILDER_SHA='3359e8b40fefb162ca4aa1d5c5a99a368a937ec61f761c3ac6f26d573766acba'
PATCH={
 (11,1):(1,1,214),(37,1):(1,1,215),(84,1):(1,1,212),
 (100,0):(0,1,211),(100,1):(1,1,221),(101,0):(0,1,92),(101,1):(1,1,174),
 (119,0):(0,1,129),(119,1):(1,1,220),(129,0):(0,1,135),(129,1):(1,1,217),
 (134,1):(1,1,228),(135,0):(0,1,166),(135,1):(1,1,96),
 (142,0):(0,1,11),(142,1):(1,1,12),(162,0):(0,1,142),
 (174,0):(0,1,227),(174,1):(1,1,143),(185,0):(0,1,224),(185,1):(1,1,172),
 (212,0):(0,1,111),(212,1):(1,1,101),(214,0):(0,1,26),(214,1):(0,-1,27),
 (215,0):(0,1,76),(215,1):(1,1,134),(221,0):(0,1,185),(221,1):(1,1,225),
 (224,0):(0,1,223),(224,1):(1,1,119),(227,0):(0,1,17),(227,1):(1,1,162),
 (228,0):(0,1,100),(228,1):(0,-1,103)}

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 for name in('baseline','parent221','sites','output'):ap.add_argument('--'+name,type=Path,required=True)
 a=ap.parse_args();require(__debug__ and not sys.flags.optimize,'Assertions must be enabled')
 parent_table=a.baseline/'machine/k219.native.tm';parent_source=a.baseline/'machine/sites219.json'
 require(sha_file(parent_table)==PARENT_TABLE_SHA and sha_file(parent_source)==PARENT_SOURCE_SHA,'Pinned published219 inputs')
 require(sha_file(a.parent221/'portable/source_language.py')==SOURCE_CODE_SHA,'Pinned source language')
 require(sha_file(a.parent221/'portable/build221.py')==BUILDER_SHA,'Pinned decoder implementation')
 sys.path.insert(0,str(a.parent221/'portable'));import source_language as s,build221 as b
 old=parse_table(parent_table.read_bytes());table=dict(old)
 require(len(PATCH)==35 and all(k in old and old[k]!=v for k,v in PATCH.items()),'Exactly35 changed rows')
 table.update(PATCH);raw=table_bytes(table);require(sha(raw)==TABLE_SHA,'Exact alternate native table')
 require(len(table)==438 and set(table)==set(old),'Same219 working states')
 source_raw=a.sites.read_bytes();require(sha(source_raw)==SOURCE_SHA,'Exact alternate source')
 rows=json.loads(source_raw);oldrows=json.loads(parent_source.read_text());tree=s.tree(rows)
 require(s.sites(tree)==rows and s.compact(rows)==source_raw,'Canonical source leaf order/bytes')
 require([row[1:]for row in rows]==[row[1:]for row in oldrows],'Every primitive operand and ordinal unchanged')
 graph=s.graph_arithmetic(rows)[0]
 require(graph==s.graph_intervals(rows)==s.graph_arithmetic(oldrows)[0]==s.graph_intervals(oldrows),'Two independently resolved complete guarded CFGs agree')
 require(s.metrics(tree)==dict(dag_nodes=206,leaf_occurrences=4744,maximum_depth=38,maximum_zero_run=6),'Exact source metrics')
 groups,paths=b.decoder_map(table,tree)
 require(len(groups)==169 and sum(map(len,groups.values()))==184,'Literal source decoder role census')
 reached={0};queue=[0]
 for q in queue:
  for bit in(0,1):
   z=table[q,bit][2]
   if z!=254 and z not in reached:reached.add(z);queue.append(z)
 require(reached=={q for q,bit in table},'All219 working states graph-reachable')
 a.output.mkdir(parents=True,exist_ok=True);(a.output/'candidate.tm').write_bytes(raw);(a.output/'sites.json').write_bytes(source_raw)
 receipt=dict(status='LITERAL_ALTERNATIVE219_AND_TWO_GUARDED_CFGS_PASS',working_states=219,transition_rows=438,changed_rows=35,
              table_sha256=TABLE_SHA,source_sha256=SOURCE_SHA,parent_table_sha256=PARENT_TABLE_SHA,parent_source_sha256=PARENT_SOURCE_SHA,
              primitive_word_equal=True,two_complete_cfg_resolvers_equal=True,source_metrics=s.metrics(tree),decoder_states=169,decoder_roles=184,
              patch=[dict(state=q,read=bit,old=old[q,bit],new=act)for(q,bit),act in sorted(PATCH.items())],
              scope='Literal construction and ordinal program equivalence. Complete unbounded primitive interfaces and exact blank initialization are separately replayed.')
 dump(a.output/'construction.json',receipt);print(receipt['status'])
if __name__=='__main__':main()
