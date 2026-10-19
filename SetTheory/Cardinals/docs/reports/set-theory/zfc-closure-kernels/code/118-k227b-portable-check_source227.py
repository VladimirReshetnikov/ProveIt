#!/usr/bin/env python3
"""Independent literal-source CFG audit; no history or source-worker imports."""
from pathlib import Path
import argparse,hashlib,json,sys

def require(value,message):
 if not value:raise ValueError(message)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def digest(value):return hashlib.sha256((json.dumps(value,separators=(',',':'))+'\n').encode()).hexdigest()
def graph(rows):
 require(isinstance(rows,list)and rows,'Missing source rows');rows=sorted(rows)
 trie={};seen=set()
 for i,row in enumerate(rows):
  require(isinstance(row,list)and len(row)==3,('Malformed leaf',row));pc,op,arg=row
  require(isinstance(pc,str)and pc and set(pc)<={'0','1'},('Invalid prefix',pc));require(pc not in seen,('Duplicate prefix',pc));seen.add(pc)
  require(op in('CI','CD','CB','CC','CH'),('Unknown operation',op))
  if op in('CI','CD'):require(type(arg)is int and 0<=arg<9,('Invalid register',arg))
  elif op in('CB','CC'):require(type(arg)is int and arg>=1,('Invalid control count',arg))
  else:require(arg is None,'Malformed halt')
  node=trie
  for b in pc:
   require('leaf'not in node,'Leaf is a prefix of another leaf');node=node.setdefault(b,{})
  require(not node,'Leaf duplicates or prefixes existing structure');node['leaf']=i
 def check(node):
  if'leaf'in node:require(set(node)=={'leaf'},'Malformed terminal');return
  require(set(node)=={'0','1'},'Incomplete binary source tree');check(node['0']);check(node['1'])
 check(trie)
 # Resolve an arbitrarily zero-padded PC by descending the literal source trie.
 def locate(word):
  node=trie;i=0
  while'leaf'not in node:
   node=node[word[i]if i<len(word)else'0'];i+=1
  require('1'not in word[i:],'Consumed source prefix has a nonzero unused tail')
  return node['leaf']
 def advance(word):
  bits=list(word);i=len(bits)-1
  while i>=0 and bits[i]=='1':bits[i]='0';i-=1
  if i>=0:bits[i]='1'
  return''.join(bits)
 def truncate(word,bit,count):
  for i in range(len(word)-1,-1,-1):
   if word[i]==bit:
    count-=1
    if not count:return word[:i]
  return''
 edges=[]
 for pc,op,arg in rows:
  if op=='CI':edge=['INC',arg,locate(advance(pc))]
  elif op=='CD':edge=['DEC',arg,locate(advance(pc)),locate(advance(truncate(pc,'0',1)))]
  elif op=='CB':edge=['JUMP',locate(advance(truncate(pc,'0',arg)))]
  elif op=='CC':edge=['JUMP',locate(truncate(pc,'1',arg))]
  else:edge=['HALT']
  edges.append(edge)
 def resolve(i):
  order=[];visited={}
  while edges[i][0]=='JUMP':
   if i in visited:return['JUMP_ONLY_CYCLE',sorted(order[visited[i]:])]
   visited[i]=len(order);order.append(i);i=edges[i][1]
  return i
 resolved=[]
 for i,e in enumerate(edges):
  if e[0]=='JUMP':continue
  if e[0]=='HALT':resolved.append([i,'HALT'])
  else:resolved.append([i,e[0],e[1],*[resolve(z)for z in e[2:]]])
 return rows,edges,locate(''),resolved,resolve(locate(''))

def expand(source):
 S=source['structures'];A={int(n):q for n,q in source['allocation'].items()};root=source['root'];out=[];internal=set();active=set()
 def visit(n,p):
  require(type(n)is int and 0<=n<len(S),('Invalid AST node',n));require(n not in active,'Cyclic AST');x=S[n];require(len(x)==2,'Malformed AST structure')
  if isinstance(x[0],str):out.append([p,*x]);return
  internal.add(n);active.add(n)
  visit(x[0],p+'0');visit(x[1],p+'1');active.remove(n)
 visit(root,'');require(set(A)==internal,('Incomplete or surplus active allocation',sorted(internal-set(A)),sorted(set(A)-internal)))
 return out,A

def main():
 require(__debug__ and not sys.flags.optimize,'Run without Python optimization')
 here=Path(__file__).resolve().parent;w=here
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--baseline-sites',type=Path,default=here/'loop_delayed228/sites.json')
 ap.add_argument('--candidate-sites',type=Path,default=here/'source_fold227_zerofix/sites.json')
 ap.add_argument('--source',type=Path,default=here/'source_fold227_zerofix/source.klabels.json')
 ap.add_argument('--klabels',type=Path,default=here/'source_fold227_zerofix/candidate.klabels.tm')
 ap.add_argument('--output',type=Path,default=here/'source_equivalence.json');a=ap.parse_args()
 require(sha(a.klabels)=='0f9e6e4458e80a9b8499de62b61bf5d5eade4e3dee1ce4bd2342bce39496ace7','Wrong repaired227 literal table')
 require(sha(a.baseline_sites)=='d8a269db4a98890c22a6da3e5cdf246f1c6b97f1acc73ec31cc46c09c23916e5','Wrong proved loop_delayed228 source')
 old=json.loads(a.baseline_sites.read_text());new=json.loads(a.candidate_sites.read_text());source=json.loads(a.source.read_text());expanded,allocation=expand(source)
 require(expanded==new,'Candidate AST does not expand to exact candidate sites')
 bo,bg,bi,br,bri=graph(old);co,cg,ci,cr,cri=graph(new)
 require([r[1:]for r in bo]==[r[1:]for r in co],'Ordered primitive occurrences changed')
 require(bg==cg and bi==ci,'Complete literal control graph differs')
 require(br==cr and bri==cri,'Jump-resolved primitive graph differs')
 require(sum(e[0]=='HALT'for e in bg)==1,'Wrong halt count')
 table={}
 for line in a.klabels.read_text().splitlines():
  if line and not line.startswith('#'):
   q,b,w,d,z=line.split();key=int(q),int(b);require(key not in table,'Duplicate table row');table[key]=(int(w),d,int(z))
 states={q for q,b in table};require(len(states)==227 and set(table)=={(q,b)for q in states for b in(0,1)},'Incomplete 227-state table')
 require(set(allocation.values())<=states,'Allocated source state missing from table')
 negative=json.loads(json.dumps(new));i=next(i for i,row in enumerate(negative)if row[1]=='CI');negative[i][2]=(negative[i][2]+1)%9
 require(graph(negative)[1]!=bg,'Changed-register negative control accepted')
 duplicate=new+[new[0]]
 try:graph(duplicate)
 except ValueError:duplicate_rejected=True
 else:duplicate_rejected=False
 require(duplicate_rejected,'Duplicate-leaf negative control accepted')
 receipt={'status':'INDEPENDENT_COMPLETE_LITERAL_AND_RESOLVED_CFG_PASS','baseline_sites_sha256':sha(a.baseline_sites),'candidate_sites_sha256':sha(a.candidate_sites),'candidate_ast_sha256':sha(a.source),'candidate_klabels_sha256':sha(a.klabels),'checker_sha256':sha(__file__),'source_leaf_occurrences':len(bg),'ordered_primitive_occurrences_identical':True,'literal_control_nodes':len(bg),'literal_control_edges':sum(2 if e[0]=='DEC'else 0 if e[0]=='HALT'else 1 for e in bg),'jump_resolved_primitive_nodes':len(br),'common_initial_leaf':bi,'common_resolved_entry':bri,'literal_cfg_sha256':digest(bg),'resolved_cfg_sha256':digest(br),'changed_prefixes':sum(x[0]!=y[0]for x,y in zip(bo,co)),'source_roles':len(allocation),'physical_source_states':len(set(allocation.values())),'complete_active_allocation':True,'all_allocated_states_defined':True,'negative_controls':{'changed_increment_register_rejected':True,'duplicate_leaf_rejected':duplicate_rejected},'theorem':'Pair the equal-ordinal primitive occurrences and use identity on all natural registers. The identical operation descriptors, every guarded successor, and entry give a stepwise bisimulation of the complete source programs, hence two-way halting equivalence for every natural initial register file.','scope':'Independent source-program equality only. Candidate history is ignored; binary runtime, startup, and state relabelings are separate obligations.'}
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
