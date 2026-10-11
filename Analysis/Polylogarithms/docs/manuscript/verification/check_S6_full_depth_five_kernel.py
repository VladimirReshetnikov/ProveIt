"""Certify the full single-X top-sector rank over Q using a finite-field minor
and 24 independently verified rational kernel vectors. This does not decide S6.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
from collections import defaultdict
import gzip,hashlib,json,math,time
import numpy as np
V=Path(__file__).resolve().parent;prime=2147483647;started=time.time()
probe_path=V/'S6-full-depth-five-probe.json.gz'
with gzip.open(probe_path,'rt',encoding='utf-8') as f:full=json.load(f)
old_path=V/'S6-depth-five-extended-probe.json';old=json.loads(old_path.read_text());kernel_path=V/'S6-depth-five-bounded-intersection.json';kernel=json.loads(kernel_path.read_text());assert kernel['status']=='PASS' and kernel['source_probe_sha256']==hashlib.sha256(old_path.read_bytes()).hexdigest()
lookup={tuple(x['input_adapted_word']):i for i,x in enumerate(full['rows'])};embedding=[]
for row in old['rows']:
 i=lookup[tuple(row['input_adapted_word'])];assert full['rows'][i]['projected_relation']==[[x['word'],x['coefficient']] for x in row['projected_relation']];embedding.append(i)
assert len(embedding)==190
leads=[];reconstruction_checks=0
for b in kernel['bounded_relations']:
 combo={embedding[z['row']]:Q(z['coefficient']) for z in b['source_combination']};lead=max(combo);leads.append(lead);assert combo[lead]!=0
 q=defaultdict(Q)
 for j,c in combo.items():
  for w,a in full['rows'][j]['projected_relation']:q[tuple(w)]+=c*Q(a)
 q={w:c for w,c in q.items() if c};expected={tuple(z['word']):Q(z['coefficient']) for z in b['integer_relation']};assert q==expected and all(sum(a!=0 for a in w)<=4 for w in q);reconstruction_checks+=1
assert len(leads)==len(set(leads))==24
# Distinct last input indices give a triangular 24-column minor of the
# rational source combinations, hence 24 independent exact top-kernel vectors.
top=[w for w in product(range(5),repeat=7) if w[0]!=4 and w[-1]!=0 and sum(x!=0 for x in w)==5 and sum(x==1 for x in w)%2];assert len(top)==6240
native=json.loads((V/'.scratch-real-orders/S6-full-top-sector-search.json').read_text());assert native['rank']==1008 and native['prime']==prime
sel=native['selected_row_indices'];cols=native['pivot_columns'];assert len(sel)==len(set(sel))==len(cols)==len(set(cols))==1008
D=json.loads((V/'S6-full-depth-five-matrix.json').read_text())['common_denominator'];assert D==5760 and math.gcd(D,prime)==1
selected_words={top[c]:j for j,c in enumerate(cols)};square=np.zeros((1008,1008),dtype=np.int64)
for i,row_id in enumerate(sel):
 for w,c in full['rows'][row_id]['projected_relation']:
  w=tuple(w)
  if w in selected_words:
   value=Q(c)*D;assert value.denominator==1;square[i,selected_words[w]]=int(value)%prime
matrix_hash=hashlib.sha256(square.astype('<i8').tobytes()).hexdigest();det=1;swaps=0
# Every multiply is a single product of two residues below 2^31, so
# multiplication and subtraction fit signed int64 exactly; no dot products.
assert (prime-1)**2+prime < 2**63
for k in range(1008):
 candidates=np.flatnonzero(square[k:,k]);assert len(candidates);pivot=k+int(candidates[0])
 if pivot!=k:square[[k,pivot],:]=square[[pivot,k],:];det=(-det)%prime;swaps+=1
 a=int(square[k,k]);det=det*a%prime;inv=pow(a,-1,prime);square[k,k:]=(square[k,k:]*inv)%prime
 factors=square[k+1:,k].copy();square[k+1:,k+1:]=(square[k+1:,k+1:]-factors[:,None]*square[None,k,k+1:])%prime;square[k+1:,k]=0
 if (k+1)%200==0:print('Independent exact modular minor',k+1,'/',1008,flush=True)
assert det!=0 and np.array_equal(np.diag(square),np.ones(1008,dtype=np.int64))
# The nonzero minor gives rank_Q >=1008; the 24 independent exact
# kernel vectors in 1032 inputs give rank_Q <=1008. Hence equality.
out=dict(status='PASS',input_rows=1032,top_columns=6240,exact_top_rank=1008,exact_kernel_dimension=24,old_rows_matched=190,exact_bounded_reconstructions=reconstruction_checks,independent_kernel_leading_indices=leads,prime=prime,common_denominator=D,minor_row_indices=sel,minor_column_indices=cols,minor_matrix_sha256=matrix_hash,minor_determinant_mod_prime=det,row_swaps=swaps,compressed_probe_sha256=hashlib.sha256(probe_path.read_bytes()).hexdigest(),old_kernel_sha256=hashlib.sha256(kernel_path.read_bytes()).hexdigest(),numpy_version=np.__version__,elapsed_seconds=round(time.time()-started,3),scope='An independently rebuilt nonzero modular minor and 24 exact rational kernel vectors prove the complete top-sector rank over Q. Consequently the previous 24 bounded relations already span every bounded-space relation obtainable from the full single-X schema modulo the Cayley ideal. This does not prove rational nonmembership of the target in the enlarged bounded span or a period nonidentity.')
(V/'S6-full-depth-five-kernel-certificate.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print('Exact top rank and kernel PASS',det,flush=True)
