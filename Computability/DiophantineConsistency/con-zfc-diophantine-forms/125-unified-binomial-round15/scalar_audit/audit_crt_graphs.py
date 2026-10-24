#!/usr/bin/env python3
"""Independent CRT-branch checker; imports only this auditor's own helpers."""
from pathlib import Path
import hashlib,json,argparse,copy,collections
from independent_audit import require,payloads,graph_check,poly_eval,norm_identity,mutations
HERE=Path(__file__).resolve().parent
BASE=HERE.parent

def upper_bound(p):
 n=p['nodes'];r=p['named_registers'];raw=[]
 for row in n:
  op=row[0];raw.append((raw[row[1]]+raw[row[2]] if op=='mul' else max(raw[row[1]],raw[row[2]])) if op in ['add','sub','mul'] else int(op=='variable'))
 expected={'Y':2,'a':4,'H':4,'Delta':8,'I':3,'Df':14,'Q':22,'V':19,'Cy':60,'Budget':16,'Dt':22,'Dg81':40,'P81':62,'M':2,'Dcar':6,'zc':7,'Ac':35,'S':16,'A':46,'B':114,'G':94}
 require(all(raw[r[k]]==v for k,v in expected.items()),'weak source degree cuts')
 if not p['description']['center']:
  require(raw[p['output']]==456,'direct upper bound')
  return {'degree_upper_bound':456,'method':'syntactic degree','prefix_degree_bounds':expected}
 # Exact source centering identity is checked by norm_identity().
 # Z^2-B=(Sn-Ac)^2+2SQV(Sn-Ac)+S^2[Q(V^2+1)-1].
 degbase=max(raw[r['S']]+1,raw[r['Ac']])
 degomega=max(2*degbase,raw[r['S']]+raw[r['Q']]+raw[r['V']]+degbase,2*raw[r['S']]+raw[r['Q']]+2*raw[r['V']])
 require(degomega==92,'omega upper bound')
 vdeg=max(degomega,raw[r['A']],raw[r['G']]);require(vdeg==94,'vnorm upper bound')
 corrected=[]
 for i,row in enumerate(n):
  op=row[0]
  dd=(corrected[row[1]]+corrected[row[2]] if op=='mul' else max(corrected[row[1]],corrected[row[2]])) if op in ['add','sub','mul'] else int(op=='variable')
  corrected.append(vdeg if i==r['vnorm'] else dd)
 require(corrected[p['output']]==416,'centered upper bound')
 return {'degree_upper_bound':416,'method':'proved universal source-center cut at vnorm, then whole-DAG propagation','omega_bound':92,'vnorm_bound':94,'prefix_degree_bounds':expected}

def carrier_mutations(packet):
 out=[]
 for label,register,slot,replacement in [('carrier loses one M factor','M4',2,'M'),('carrier base HM becomes H+M','Dcar',0,'add')]:
  p=copy.deepcopy(packet)
  p['nodes'][p['named_registers'][register]][slot]=p['named_registers'][replacement] if slot else replacement
  counts=collections.Counter(r[0] for r in p['nodes'] if r[0] in ['add','sub','mul']);p['operation_counts']=dict(counts);p['operations']=sum(counts.values())
  deg=[]
  for row in p['nodes']:
   op=row[0];deg.append((deg[row[1]]+deg[row[2]] if op=='mul' else max(deg[row[1]],deg[row[2]])) if op in ['add','sub','mul'] else int(op=='variable'))
  p['syntactic_degree_bound']=deg[p['output']]
  try:graph_check(p,True)
  except ValueError as e:out.append({'name':label,'rejected':True,'reason':str(e)})
  else:raise ValueError('carrier mutation accepted')
 return out

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,default=HERE/'CRT_AUDIT_RESULTS.json');args=ap.parse_args()
 directory=BASE/'norm_weak';coeff=directory/'coefficients'
 if not coeff.exists():coeff=BASE/'norm'/'coefficients'
 values=payloads(coeff)
 result={'status':'PASS','source_proof':'../scalar/CRT_CARRIER_PROOF.md','semantic_review':'CRT_CARRIER_AUDIT.md','identities':norm_identity(),'graphs':{}}
 for name in ['weak_integral_centered_paired','weak_integral_direct_paired']:
  path=directory/(name+'.json');p=json.loads(path.read_text());row=graph_check(p,True);row.update(upper_bound(p));row['degree_lower_bound']=poly_eval(p,values,weak=True);row['sha256']=hashlib.sha256(path.read_bytes()).hexdigest();result['graphs'][name]=row
  if p['description']['center']:result['mutation_controls']=mutations(p,True)+carrier_mutations(p)
 args.out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
