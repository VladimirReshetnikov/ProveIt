#!/usr/bin/env python3
"""Identify exact source-subtree counterparts needed for ProveIt238-to237.

This is a literal portability audit, not a lower bound or a complete search.
Paths are explicit command-line arguments; external programs are not imported.
"""
from pathlib import Path
from collections import defaultdict
import argparse,hashlib,json

def table(path):
 t={}
 for ln in Path(path).read_text().splitlines():
  if ln and not ln.startswith('#'):
   q,b,w,d,z=ln.split();t[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(z))
 return t

def tree(rows):
 root={}
 for p,o,r in rows:
  at=root
  for c in p:at=at.setdefault(c,{})
  assert not at;at['leaf']=(o,r)
 def cv(n):
  if'leaf'in n:assert set(n)=={'leaf'};return n['leaf']
  assert set(n)=={'0','1'};return cv(n['0']),cv(n['1'])
 return cv(root)

def leaf(n):return isinstance(n[0],str)
def source_counts(root):
 counts=defaultdict(int)
 def visit(n):
  if leaf(n):return
  counts[n]+=1;visit(n[0]);visit(n[1])
 visit(root);return counts
def mapping(root,t,start):
 mp=defaultdict(set);byq=defaultdict(set)
 def visit(n,q):
  if leaf(n) or q in mp[n]:return
  mp[n].add(q);byq[q].add(n)
  for b in(0,1):
   w,d,z=t[q,b]
   if(w,d)==(b,1):visit(n[b],z)
 visit(root,start);return mp,byq

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--old-table',required=True);p.add_argument('--old-sites',required=True);p.add_argument('--k-table',required=True);p.add_argument('--k-sites',required=True);p.add_argument('--output',required=True);a=p.parse_args()
o=table(a.old_table);k=table(a.k_table);os=json.loads(Path(a.old_sites).read_text());ks=json.loads(Path(a.k_sites).read_text())
old_tree=tree(os);k_tree=tree(ks)
om,ob=mapping(old_tree,o,96);km,kb=mapping(k_tree,k,84);k_counts=source_counts(k_tree)
labels=(16,23,87,98,99,113,139,156,164,176,190,231,235,240)
counterparts={q:sorted(set().union(*(km.get(n,set()) for n in ob[q]))) for q in labels}
records={q:{'old_rows':[o[q,0],o[q,1]],'number_of_old_source_subtrees':len(ob[q]),'exact_subtree_occurrences_anywhere_in_k_source':sum(k_counts[n] for n in ob[q]),'exact_k_source_subtree_counterparts':counterparts[q],'counterpart_rows':{z:[k[z,0],k[z,1]] for z in counterparts[q]}} for q in labels}
same_one12=[{'state':q,'rows':[k[q,0],k[q,1]]} for q in sorted({q for q,b in k}) if k[q,1]==(1,1,12)]
# The uniquely identified helper and its unchanged children genuinely transfer.
assert counterparts[16]==[12] and counterparts[113]==[98] and counterparts[176]==[147] and counterparts[99]==[86] and counterparts[240]==[186]
require98=(0,1,98),(1,1,12)
exact98=[q for q in sorted({q for q,b in k}) if(k[q,0],k[q,1])==require98]
out={'status':'EXACT_PORTABILITY_PRECONDITIONS_AUDITED','old_table_sha256':sha(a.old_table),'old_sites_sha256':sha(a.old_sites),'k_table_sha256':sha(a.k_table),'k_sites_sha256':sha(a.k_sites),'labels':records,'expected_native_boundary98_rows':require98,'native_states_with_exact_boundary98_rows':exact98,'native_states_sharing_the_required_read1':same_one12,'conclusion':'The helper old240 has exact K counterpart186, but the full shared-helper template has no unchanged direct port: its boundary-state98 source role is absent. The old235 and old87 source counterparts are listed explicitly; missing roles require source restructuring or a new semantic argument. This audit rules out only literal reuse of the specified template.'}
Path(a.output).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
