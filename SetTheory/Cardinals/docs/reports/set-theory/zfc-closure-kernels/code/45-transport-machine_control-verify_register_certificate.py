#!/usr/bin/env python3
"""Check a supplied RM invariant without constructing its fixpoint.

Independent implementation: no import of register_abstract or its producer.
The checker verifies the initial vector and every abstract control edge. The
report states and proves the induction transporting these finite checks to
all actual finite register runs. No proof-assistant claim is made.
"""
import argparse,hashlib,json,re
from pathlib import Path

EXPECTED='1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'
def need(x,message):
 if not x:raise ValueError(message)

def check(program,certificate):
 data=program.read_bytes();need(hashlib.sha256(data).hexdigest()==EXPECTED,'wrong input program')
 proof=json.loads(certificate.read_text());need(proof['program_sha256']==EXPECTED,'wrong certificate input')
 K=proof['cutoff'];need(type(K)is int and 0<=K<=31,'bad cutoff')
 full=(1<<(K+2))-1;ann=proof['invariant'];need(len(ann)==6460,'wrong annotation count')
 for s in ann:
  need(s is None or len(s)==9 and all(type(x)is int and 0<x<=full for x in s),'bad vector')
 text=data.decode().split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
 raw=re.findall(r'\((C[A-Z](?: \d+)?),\s*(C[A-Z](?: \d+)?)\)',text)
 need(len(raw)==6459,'wrong node count')
 nodes=[tuple((e.split()[0],int(e.split()[1]) if len(e.split())>1 else None) for e in row) for row in raw]
 leaves=[]
 def walk(q,bits):
  for digit,(op,r) in enumerate(nodes[q]):
   p=bits+[digit]
   if op=='CN':need(q<r<6459,'input is not a forward tree');walk(r,p)
   else:leaves.append((tuple(p),op,r))
 walk(0,[]);need(len(leaves)==6460,'wrong leaf count')
 bypath={p:i for i,(p,_,_) in enumerate(leaves)}
 def lookup(bits):
  node=0;used=[];at=0
  while True:
   b=bits[at] if at<len(bits) else 0;used.append(b);at+=1
   op,n=nodes[node][b]
   if op!='CN':return bypath[tuple(used)]
   node=n
 def bump(bits):
  out=list(bits)
  for j in range(len(out)-1,-1,-1):
   out[j]^=1
   if out[j]:break
  return out
 def remove(bits,digit,k):
  out=list(bits)
  while out and k:
   k-=out.pop()==digit
  return out
 initial=proof['initial_nextproof'];need(type(initial)is int and initial>=0,'bad initial value')
 initial=[initial]+[0]*8;start=lookup([])
 need(ann[start] is not None,'initial site unreachable')
 need(all(ann[start][r]&(1<<min(x,K+1)) for r,x in enumerate(initial)),'initial vector excluded')
 obligations=0;forced=[];unreachable=[]
 for i,(path,op,r) in enumerate(leaves):
  s=ann[i]
  if s is None:unreachable.append(i);continue
  if op=='CH':continue
  if op=='CI':branches=[('inc',bump(path))]
  elif op=='CD':branches=[('zero',bump(remove(path,0,1))),('positive',bump(path))]
  elif op=='CB':branches=[('identity',bump(remove(path,0,r)))]
  elif op=='CC':branches=[('identity',remove(path,1,r))]
  else:raise ValueError('unknown leaf')
  for kind,word in branches:
   target=lookup(word);new=list(s)
   if kind!='identity':
    mask=0
    for atom in range(K+2):
     if not s[r]&(1<<atom):continue
     if kind=='zero':outputs=[0] if atom==0 else []
     elif kind=='inc':outputs=[min(K+1,atom+1)]
     elif atom==0:outputs=[]
     elif atom==K+1:outputs=[K,K+1]
     else:outputs=[atom-1]
     for o in outputs:mask|=1<<o
    if mask==0:continue
    new[r]=mask
   need(ann[target] is not None,'reachable edge enters bottom annotation')
   need(all(a&~b==0 for a,b in zip(new,ann[target])),f'edge closure failed at site {i}, {kind}')
   obligations+=1
  if op=='CD' and s[r]==1:forced.append([i,''.join(map(str,path)),r,'zero'])
  elif op=='CD' and s[r]&1==0:forced.append([i,''.join(map(str,path)),r,'positive'])
 listed=[[x['site'],x['path'],x['register'],x['branch']] for x in proof['forced_decrements']]
 need(listed==forced,'forced-branch summary differs')
 need(unreachable==proof['unreachable_sites'],'unreachable summary differs')
 need(obligations==proof['checked_inductive_edges'],'edge count differs')
 coalescing=[]
 for r in range(9):
  for other in range(r+1,9):
   obstructions=[]
   for i,(_,op,touched) in enumerate(leaves):
    if ann[i] is None or op not in ('CI','CD') or touched not in (r,other):continue
    untouched=other if touched==r else r
    if ann[i][untouched]!=1:
     obstructions.append({'site':i,'touched':touched,'other_mask':ann[i][untouched]})
     if len(obstructions)==3:break
   coalescing.append({'registers':[r,other],'coalescing_certified':not obstructions,'obstructions':obstructions})
 need(coalescing==proof['register_coalescing'],'coalescing summary differs')
 return {'passed':True,'nextproof':initial[0],'cutoff':K,'reachable_sites':len(ann)-len(unreachable),
         'inductive_edge_obligations':obligations,'forced':forced,
         'root_first_site':start,'root_first_path':''.join(map(str,leaves[start][0])),
         'root_entry_masks':ann[start],
         'forced_entry_masks':{str(i):ann[i] for i,_,_,_ in forced},
         'zero_instruction_positions_per_register':[sum(s is not None and s[r]==1 for s in ann) for r in range(9)],
         'coalescible_pairs_under_test':[x['registers'] for x in coalescing if x['coalescing_certified']],
         'certificate_sha256':hashlib.sha256(certificate.read_bytes()).hexdigest()}

def main():
 a=argparse.ArgumentParser(description=__doc__);a.add_argument('program',type=Path);a.add_argument('certificate',type=Path)
 a.add_argument('--output',type=Path)
 v=a.parse_args();result=json.dumps(check(v.program,v.certificate),indent=2)+'\n'
 if v.output:v.output.write_text(result)
 print(result,end='')
if __name__=='__main__':main()
