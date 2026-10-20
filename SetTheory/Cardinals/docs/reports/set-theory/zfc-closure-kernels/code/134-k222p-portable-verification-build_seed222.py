#!/usr/bin/env python3
"""Deterministic compiler and two-fold construction of the seed+G 222 machine.

Use --parent-table and --parent-sites for the pinned K224 inputs and --sites
for the independently certified seed+G source. All paths are explicit. No
optimization search occurs. Exact source/compiler/runtime proofs are separate.
"""
from pathlib import Path
from collections import defaultdict,Counter
import argparse,hashlib,json

PARENT_TABLE_SHA='f886dd8d11e9705c5315140f68d5ae2f26c80afb015e08074c7e3da1414fa37f'
PARENT_SOURCE_SHA='309358206463f8e8d88d86304e7c9f2273e3cdde64984b6db20c412516010878'
SOURCE_SHA='cc1fbb3a16dd446af9c7cdb678317d31060082e6794b9c7074ce02b46584a75e'
FINAL_SHA='3bcf4678c9c576ae99a108c32038f035b42204289267d05a34ba2b37b32b6476'
HALT=254

def need(c,m):
 if not c:raise ValueError(m)

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def dump(p,v):Path(p).write_text(json.dumps(v,indent=2)+'\n')
def leaf(n):return isinstance(n[0],str)
def tree(rows):
 d={p:(op,a) for p,op,a in rows}
 def rec(p):return d[p] if p in d else (rec(p+'0'),rec(p+'1'))
 return rec('')
def read_table(p):
 t={};start=[]
 for ln in Path(p).read_text().splitlines():
  if ln.startswith('#! start '):start.append(int(ln.split()[-1]));continue
  if not ln or ln.startswith('#'):continue
  q,b,w,d,z=ln.split();q,b,w,z=map(int,(q,b,w,z))
  need((q,b) not in t and b in (0,1) and w in (0,1) and d in ('L','R'),'invalid row')
  t[q,b]=(w,1 if d=='R' else -1,z)
 qs={q for q,b in t};need(start==[0] and set(t)=={(q,b) for q in qs for b in (0,1)},'table format')
 need({z for w,d,z in t.values()}-qs=={HALT},'halt convention')
 return t

def table_bytes(t,start=0):return ('#! start %d\n'%start+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n' for (q,b),(w,d,z) in sorted(t.items()))).encode()

def decoder(t,root):
 groups=defaultdict(set);paths=defaultdict(list);helpers=set()
 def visit(n,p,q):
  if leaf(n):return
  groups[q].add(n);paths[q].append(p)
  for b,ch in enumerate(n):
   if leaf(ch):continue
   tape={i:int(c) for i,c in enumerate(p+str(b))};tape[-1]=1
   before=tape.copy();h=len(p);z=q
   for tick in range(100):
    if h==len(p)+1:break
    need(h in tape,'decoder reads unknown exterior')
    if tick:helpers.add(z)
    w,d,z=t[z,tape[h]];tape[h]=w;h+=d
   need(tape==before and h==len(p)+1,'decoder changes prefix or fails to advance')
   visit(ch,p+str(b),z)
 visit(root,'',84)
 return groups,paths,helpers

def compile_source(old,oldtree,newtree):
 groups,paths,protected=decoder(old,oldtree);oldmap={n:q for q,ns in groups.items() for n in ns}
 nodes=set()
 def collect(n):
  if n in nodes or leaf(n):return
  nodes.add(n);collect(n[0]);collect(n[1])
 collect(newtree)
 intended={n:oldmap[n] for n in nodes if n in oldmap};occupied=set(intended.values())
 def align(before,after):
  if leaf(before) or leaf(after):return
  q=oldmap[before]
  if after not in intended and q not in occupied and len(groups[q])==1 and q not in protected:
   intended[after]=q;occupied.add(q)
  align(before[0],after[0]);align(before[1],after[1])
 align(oldtree,newtree);need(intended.get(newtree,84)==84,'root conflict');intended[newtree]=84;occupied.add(84)
 free=sorted(set(groups)-occupied-protected,key=lambda q:(any(d!=1 or w!=b for b,(w,d,z) in enumerate((old[q,0],old[q,1]))),q))
 fresh=max(300,max(q for q,b in old)+1)
 def assign(n):
  nonlocal fresh
  if leaf(n):return
  if n not in intended:
   if free:intended[n]=free.pop(0)
   else:intended[n]=fresh;fresh+=1
  assign(n[0]);assign(n[1])
 assign(newtree);table=dict(old)
 def primitive(ch,b):
  choices=Counter(old[q,b] for n,q in oldmap.items() if n[b]==ch)
  direct=[act for act,count in choices.items() if act[:2]==(b,1)]
  if len(direct)==1:return direct[0]
  op,a=ch
  if op=='CC' and b==1:return 0,-1,{1:1,2:16,3:42}[a]
  if op=='CB' and a==1 and b==1:return 0,-1,40
  if op=='CH' and b==1:return 1,1,HALT
  raise ValueError(('unsupported primitive',ch,b))
 for n,q in intended.items():
  if n in oldmap:continue
  for b,ch in enumerate(n):
   alts=groups.get(q,set())
   if len(alts)==1 and next(iter(alts))[b]==ch:continue
   table[q,b]=primitive(ch,b) if leaf(ch) else (b,1,intended[ch])
 actual,newpaths,_=decoder(table,newtree);expected=defaultdict(set)
 for n,q in intended.items():expected[q].add(n)
 need(actual==expected,'actual decoder relation differs from intended relation')
 need(all(table[q,b]==old[q,b] for q in protected for b in (0,1)),'helper overwritten')
 reachable={0};todo=[0]
 for q in todo:
  for b in (0,1):
   z=table[q,b][2]
   if z!=HALT and z not in reachable:reachable.add(z);todo.append(z)
 table={k:v for k,v in table.items() if k[0] in reachable}
 receipt=dict(status='LITERAL_SOURCE_DECODER_RECONSTRUCTION_PASS',states=len(table)//2,rows=len(table),decoder_nodes=len(nodes),decoder_states=len(actual),alias_savings=sum(len(v)-1 for v in actual.values()),protected_helper_states=sorted(protected),compound_prefixes=sum(map(len,newpaths.values())),fresh_labels=fresh-300,scope='Exact decoder relation and preservation of inherited decoder helper rows; instruction runtime and theory calibration require separate certificates.')
 return table,receipt

def fold(t,keep,drop,a0,a1):
 ph=lambda q:keep if q==drop else q
 r={(q,b):(w,d,ph(z)) for (q,b),(w,d,z) in t.items() if q!=drop}
 r[keep,0]=(a0[0],a0[1],ph(a0[2]));r[keep,1]=(a1[0],a1[1],ph(a1[2]))
 return r

def canonical(t):
 todo=[0];mp={0:0}
 for q in todo:
  for b in (0,1):
   z=t[q,b][2]
   if z!=HALT and z not in mp:mp[z]=len(mp);todo.append(z)
 need(set(mp)=={q for q,b in t},'unreachable declared state');mp[HALT]=len(todo)
 return {(mp[q],b):(w,d,mp[z]) for (q,b),(w,d,z) in t.items()},mp

def bootstrap(table):
    q=0;head=0;ones=set()
    for tick in range(409835):
        need(q!=254, 'Premature halt during initialization')
        b=int(head in ones);w,d,q=table[q,b]
        if w:ones.add(head)
        else:ones.discard(head)
        head+=d
    need(q==84 and head==-5, 'Blank bootstrap endpoint differs')
    need(min(ones)==head-1, 'Nonblank tape to the left of the marker')
    # At this checked dispatcher the address is empty. The first right-hand 1
    # marks the end of the zero gap; B(v)=0 1^(v+1) encodes each register.
    header=min(x for x in ones if x>=head); pos=header+1; values=[]
    while pos<=max(ones):
        need(pos not in ones and pos+1 in ones, 'Malformed unary register block')
        pos+=1;start=pos
        while pos in ones:pos+=1
        values.append(pos-start-1)
    need(pos==max(ones)+1 and len(values)==176, 'Wrong register/spare count')
    physical=[0]*9
    logical=[3,0,0,0,3,0,0,0,0]
    permutation=[6,2,0,4,3,7,8,5,1]
    for i,j in enumerate(permutation):physical[j]=logical[i]
    need(values[:9]==physical and values[9:]==[1]*167, 'Wrong initialized registers')
    need(header-head==181 and len(ones)==351, 'Wrong initialized gap or support')
    return dict(status='EXACT_BLANK_BOOTSTRAP_PASS',steps=409835,k_state=q,head=head,
        logical_registers=logical,physical_register_map=permutation,zero_gap=181,extra_gap=117,
        spare_count=167,spare_values=1,one_cells=sorted(ones),one_cell_count=len(ones),
        all_unlisted_cells=0,scope='Exact complete tape after the first 409835 blank-start transitions.')

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 for a in ('parent-table','parent-sites','sites','output-dir'):ap.add_argument('--'+a,type=Path,required=True)
 ap.add_argument('--legacy-map',type=Path)
 a=ap.parse_args();need(__debug__,'Keep Python assertions enabled')
 need(sha(a.parent_table)==PARENT_TABLE_SHA,'wrong parent table');need(sha(a.parent_sites)==PARENT_SOURCE_SHA,'wrong parent source');need(sha(a.sites)==SOURCE_SHA,'wrong new source')
 old=read_table(a.parent_table);parent,receipt=compile_source(old,tree(json.loads(a.parent_sites.read_text())),tree(json.loads(a.sites.read_text())))
 need(len(parent)==448,'expected 224-state seed+G parent')
 final=fold(parent,118,185,(0,1,155),(1,1,153));final=fold(final,159,174,(0,1,166),(1,1,118));can,mp=canonical(final)
 out=a.output_dir;out.mkdir(parents=True,exist_ok=True)
 (out/'parent_seed_g224.k.tm').write_bytes(table_bytes(parent));(out/'candidate222.k.tm').write_bytes(table_bytes(final));(out/'candidate222.tm').write_bytes(table_bytes(can));(out/'sites.json').write_bytes(a.sites.read_bytes())
 need(len(can)==444 and sha(out/'candidate222.tm')==FINAL_SHA,'final candidate differs')
 maps=dict(k_to_canonical=mp)
 if a.legacy_map:
  raw=json.loads(a.legacy_map.read_text());legacy={int(q):v for q,v in raw['k230_to_old'].items()};legacy[HALT]=HALT
  lt={(legacy[q],b):(w,d,legacy[z]) for (q,b),(w,d,z) in final.items()};(out/'candidate222.legacy.tm').write_bytes(table_bytes(lt,95));maps['k_to_legacy']=legacy
 dump(out/'state_map.json',maps);boot=bootstrap(final);dump(out/'bootstrap.json',boot);receipt['bootstrap_steps']=boot['steps'];receipt['canonical_dispatcher']=mp[84];receipt['canonical_sha256']=FINAL_SHA;receipt['source_sha256']=SOURCE_SHA;receipt['final_states']=222
 dump(out/'compile_receipt.json',receipt);print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
