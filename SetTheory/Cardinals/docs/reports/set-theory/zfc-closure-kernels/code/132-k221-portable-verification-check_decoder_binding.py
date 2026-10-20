#!/usr/bin/env python3
"""Bind an untrusted node-allocation witness to exact source and literal rows.
Standard library plus the adjacent independent parsers only. This verifies all
compound decoder edges, not primitive execution or startup. No search imports.
"""
from pathlib import Path
import argparse,copy,json
from audit_decoder_contexts import table,advance
from check_grammar_equivalence import validate,need,sha

def check(rows,T,A):
 validate(rows);S=A['structures'];root=A['root'];M={int(k):v for k,v in A['allocation'].items()};seen=set();active=set();sites=[];paths={}
 def visit(n,p):
  need(type(n)is int and 0<=n<len(S),'node index');need(n not in active,'cyclic structure');x=S[n];need(isinstance(x,list)and len(x)==2,'node shape')
  if isinstance(x[0],str):sites.append([p,*x]);return
  need(n in M and type(M[n])is int,'missing allocation');need((M[n],0)in T and(M[n],1)in T,'allocated state lacks rows');active.add(n);seen.add(n);paths.setdefault(n,[]).append(p)
  visit(x[0],p+'0');visit(x[1],p+'1');active.remove(n)
 visit(root,'');need(sites==rows,'allocation structure differs from exact source');need(set(M)==seen,'extraneous allocation');need(M[root]==84,'dispatcher binding')
 total=0;maxsteps=0;fail=[];aliases={}
 for n,ps in paths.items():
  q=M[n];aliases.setdefault(q,[]).append(n)
  for b,ch in enumerate(S[n]):
   if isinstance(S[ch][0],str):continue
   for p in ps:
    r=advance(T,q,p,b);total+=1;maxsteps=max(maxsteps,len(r['trace']))
    if not(r['ok']and r.get('state')==M[ch]):fail.append(dict(node=n,state=q,bit=b,prefix=p,expected_state=M[ch],actual=r))
 need(not fail,'compound decoder mismatch: '+json.dumps(fail[:2],separators=(',',':')))
 states={q for q,b in T};need(all((q,b)in T for q in states for b in(0,1)),'incomplete table');need(all(z in states or z==254 for w,d,z in T.values()),'undefined target')
 return dict(status='INDEPENDENT_EXACT_SOURCE_DECODER_BINDING_PASS',source_leaves=len(rows),internal_nodes=len(seen),allocated_decoder_states=len(aliases),alias_saving=len(seen)-len(aliases),alias_groups={str(q):ns for q,ns in aliases.items()if len(ns)>1},compound_occurrence_cases=total,maximum_compound_steps=maxsteps,table_states=len(states),scope='Exact allocation-to-source identity and every compound decoder edge on every concrete source prefix, with prefix tape restoration. Unknown-context reads reject. Primitive execution and blank startup are separate obligations.')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,required=True);ap.add_argument('--allocation',type=Path,required=True);ap.add_argument('--table',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();rows=json.loads(a.source.read_bytes());A=json.loads(a.allocation.read_bytes());T=table(a.table);out=check(rows,T,A);negative=[]
 # Untrusted witness mutation must be detected even if table is unchanged.
 B=copy.deepcopy(A);B['root']=-1
 try:check(rows,T,B)
 except (ValueError,KeyError,IndexError)as e:negative.append(dict(name='invalid_allocation_root',status='REJECTED',reason=str(e)))
 else:raise ValueError('negative allocation control accepted')
 # Corrupt a compound row at the root, making it enter halt instead of decoder.
 U=T.copy();S=A['structures'];root=A['root'];b=next(b for b,ch in enumerate(S[root])if not isinstance(S[ch][0],str));U[84,b]=(b,1,254)
 try:check(rows,U,A)
 except (ValueError,KeyError,IndexError)as e:negative.append(dict(name='compound_transition_to_halt',status='REJECTED',reason=str(e)))
 else:raise ValueError('negative decoder control accepted')
 out.update(source_sha256=sha(a.source.read_bytes()),allocation_sha256=sha(a.allocation.read_bytes()),table_sha256=sha(a.table.read_bytes()),checker_sha256=sha(Path(__file__).read_bytes()),negative_controls=negative);a.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
