#!/usr/bin/env python3
"""Expose all AX macro cutpoints and prove their finite CFG transplantation.

This checks syntax and resolved successor identities against the pinned primary
source. The semantic helper contracts are inherited, not established here.
"""
from pathlib import Path
import argparse,json,sys,hashlib,collections

def build(candidate):
 sys.path.insert(0,str(candidate/'verification/reference'))
 import source_language as lang
 baseline=json.loads((candidate/'inputs/primary.nodes.json').read_text())
 nodes=json.loads((candidate/'machine/nodes.json').read_text())
 grammar=json.loads((candidate/'machine/grammar.tree.json').read_text())
 primaryg=json.loads((candidate/'inputs/primary.grammar.json').read_text())
 def gexpand(x):
  return [gexpand(y)for y in primaryg['rules'][x]]if isinstance(x,str)and x in primaryg['rules']else x
 oldg=gexpand(primaryg['root'])
 def expandall(ns,g):
  sites=[];visits={}
  def go(t,path):
   if isinstance(t,str):
    lo=len(sites);go(g if t=='x67'else ns[t],path)
    visits.setdefault(t,[]).append({'path':path,'start':lo,'end_exclusive':len(sites)});return
   if t[0]=='leaf':sites.append([path,t[1],t[2]]);return
   assert len(t)==2
   go(t[0],path+'0');go(t[1],path+'1')
  go('node172','');return sites,visits
 oldsites,oldvisits=expandall(baseline,oldg);sites,visits=expandall(nodes,grammar)
 assert sites==json.loads((candidate/'machine/sites.json').read_text())
 def graph(s):
  ops={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
  mapped=[[p,ops[o],a]for p,o,a in s]
  x,_=lang.graph_arithmetic(mapped);assert x==lang.graph_intervals(mapped)
  names={'identity':'jump','increment':'inc','decrement':'dec','halt':'halt'}
  return [[names[e[0]]]+e[1:]+ts for e,ts in x]
 old=graph(oldsites);new=graph(sites)
 assert new==json.loads((candidate/'machine/instructions.json').read_text())
 ax=visits['x67'];assert len(ax)==1
 plan=[]
 def scan(t,path):
  if isinstance(t,str)or t[0]=='leaf':
   indexes=[i for i,s in enumerate(sites)if s[0].startswith(path)]
   lo,hi=min(indexes),max(indexes)+1;assert indexes==list(range(lo,hi))
   plan.append({'token':t,'path':path,'start':lo,'end_exclusive':hi});return
  scan(t[0],path+'0');scan(t[1],path+'1')
 scan(grammar,ax[0]['path']);assert len(plan)==190
 def targets(row):return row[2:]if row[0]in('inc','dec')else row[1:]
 def normalized(ins,lo,hi):
  result=[]
  for row in ins[lo:hi]:
   k=2 if row[0]in('inc','dec')else 1
   assert all(lo<=t<=hi for t in row[k:])
   result.append(row[:k]+[t-lo for t in row[k:]])
  return result
 prototypes={};primitives=0
 for item in plan:
  lo,hi=item['start'],item['end_exclusive'];token=item['token']
  outgoing=sorted({t for row in new[lo:hi]for t in targets(row)if not lo<=t<hi})
  incoming=sorted({t for i,row in enumerate(new)if not lo<=i<hi for t in targets(row)if lo<=t<hi})
  assert incoming==[lo]and outgoing==[hi]
  item['incoming_entry_targets']=incoming;item['outgoing_targets']=outgoing
  n=normalized(new,lo,hi)
  if isinstance(token,list):
   assert token==['leaf','inc',1]and n==[['inc',1,1]]
   item['baseline_relative_identity']='primitive increment register1';primitives+=1;continue
  prototype=oldvisits[token][0];oldlo,oldhi=prototype['start'],prototype['end_exclusive']
  o=normalized(old,oldlo,oldhi);assert n==o
  digest=hashlib.sha256(json.dumps(n,separators=(',',':')).encode()).hexdigest()
  item['baseline_prototype']={'node':token,'start':oldlo,'end_exclusive':oldhi}
  item['normalized_cfg_sha256']=digest;item['normalized_cfg_equal_to_baseline_helper']=True
  prototypes[token]={'baseline_first_interval':[oldlo,oldhi],'primitive_sites':oldhi-oldlo,'normalized_cfg':o,'sha256':digest}
 assert primitives==57 and len(prototypes)==9
 cutpoints={'root':visits['node171'][0]['start'],'AX':ax[0]['start'],'MP':visits['node164'][0]['start'],
            'return':visits['node166'][0]['end_exclusive']-1,'Shift':visits['node167'][0]['end_exclusive']}
 assert cutpoints=={'root':25,'AX':50,'MP':3572,'return':3659,'Shift':3660}
 assert new[cutpoints['return']]==['jump',25]
 return {'status':'PASS','scope':'Exact source syntax/CFG transplantation; semantic helper contracts are inherited separately.',
         'source_sha256':hashlib.sha256((candidate/'machine/sites.json').read_bytes()).hexdigest(),
         'source_sites':len(sites),'command_cutpoints':cutpoints,'AX_interval':ax[0],
         'AX_tokens':190,'named_helper_occurrences':133,'primitive_increments':57,
         'all_macro_instances_single_entry_and_next_token_exit':True,
         'all_macro_cfgs_equal_to_baseline_helper':True,'macros':plan,
         'baseline_helper_prototypes':prototypes}

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--candidate',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 assert __debug__
 result=build(a.candidate);a.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items()if k not in ('macros','baseline_helper_prototypes')},indent=2))
if __name__=='__main__':main()
