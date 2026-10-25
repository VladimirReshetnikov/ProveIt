#!/usr/bin/env python3
"""Deterministic centered-norm DAG builder; reads retained specs as data only."""
import json
from pathlib import Path
from circuit import DAG,export
ROOT=Path(__file__).resolve().parent
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
def build(tag,old,degree,tail):
 s=json.loads((ROOT/'inherited'/(old+'_spec.json')).read_text())
 drop={'carrier','UG','U2','ga','db','fc','gc','inner','N','P','Dt'}
 regs=[(n,f) for n,f in s['registers'] if n not in drop]+tail
 d=DAG(s['variables']);env={x:d.leaf('variable',x) for x in s['variables']}
 env.update({x:d.leaf('coefficient',x) for x in PORTS})
 for n,f in regs:env[n]=eval(f,{'__builtins__':{}},env)
 p=export(tag,d,env['P'],{n:env[n] for n,f in regs}, {'exact_degree':degree,'fixed_numerals':PORTS,'proof':'PROOF.md','proof_status':'Ordinary universal polynomial shear and signed zero maps; inherited native/refutation theorem, no new kernel certificate.'})
 p['coefficient_binding']='inherited/baseline/coefficients/BINDING.json'
 (ROOT/(tag+'.json')).write_text(json.dumps(p,indent=2,sort_keys=True)+'\n')
 (ROOT/(tag+'_spec.json')).write_text(json.dumps({'variables':s['variables'],'registers':regs,'degree':degree},indent=2)+'\n')
 return {k:p[k] for k in ['name','variable_count','exact_degree','operations','operation_counts']}
def main():
 common=[('Dt','1+L*(L+k)'),('U2','U**2'),('ga','U2*G'),('db','4*U2*Dt')]
 rows=[build('integer14_degree88_ops110','integer14_degree88_ops115',88,common+[
 ('N','(Z**2-ga-db)**2-4*ga*db'),('P','(N+1)*strong*auxiliary-1')]),
 build('integer13_degree156_ops117','integer13_degree156_ops125',156,common+[
 ('fc','16*U2*Fs'),('gad','ga*db'),('gab','ga+db'),('Z2','Z**2'),
 ('inner','(Z2-gab-fc)**2-4*(gad+gab*fc)'),
 ('N','inner**2-64*gad*fc*Z2'),('P','(N+1)*auxiliary-1')])]
 (ROOT/'METRICS.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows))
if __name__=='__main__':main()
