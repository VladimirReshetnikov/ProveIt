#!/usr/bin/env python3
"""Read-only local-source audit for the exact K230 mathematical endpoint.

This checks pinned local bytes, literal theorem-chain declarations, and absence
of source-level axiom/admit/unchecked-conversion constructs. It does not replace
Rocq compilation or Print Assumptions on the compiled final declarations.
"""
from pathlib import Path
import argparse,hashlib,json,re

def require(p,m):
 if not p:raise ValueError(m)

def uncomment(text):
 out=[];i=0;depth=0;string=False
 while i<len(text):
  if depth:
   if text.startswith('(*',i):depth+=1;out.extend('  ');i+=2
   elif text.startswith('*)',i):depth-=1;out.extend('  ');i+=2
   else:out.append('\n'if text[i]=='\n'else' ');i+=1
  elif string:
   if text[i]=='"':
    if text.startswith('""',i):out.extend('  ');i+=2;continue
    string=False
   out.append(' ');i+=1
  elif text.startswith('(*',i):depth=1;out.extend('  ');i+=2
  elif text[i]=='"':string=True;out.append(' ');i+=1
  else:out.append(text[i]);i+=1
 require(depth==0 and not string,'unterminated Coq comment/string')
 return ''.join(out)

CHAIN={
 'coq/tm/Correct230.v':['tm230_halts_iff_ZFC_inconsistent','tm230_nonhalting_iff_ZFC_consistent','Sim230Main.tm230_rm','prog230','seed230_iff_thm','thm230_iff_standardZFC'],
 'coq/tm/Sim230Main.v':['tm230_rm','inv_boot','inv_step','inv_halt'],
 'coq/prog/Main230.v':['prog230','p230_dag','iter_halts_dag','R0_enc_seed230'],
 'coq/logic/Seed230.v':['seed230_complete','seed230_sound','seed230_iff_thm','mkState 0 3 0 0 3 0'],
 'coq/logic/Consistency230.v':['thm230_iff_standardZFC','thm230_iff_KPrimeOrdIR','KPrimeOrdIR_standardZFC_equiconsistent'],
 'coq/logic/Bridge230.v':['thm230_iff_KPrimeOrdIR','decodedIR_to_KPrimeOrdIR','KPrimeOrdIR_to_thm'],
 'coq/settheory/KUpperConsistency.v':['KPrimeOrdIR_standardZFC_inconsistent','KPrimeOrdIR_standardZFC_equiconsistent','KPrimeOrd_standardZFC_equiconsistent','KPrimeOrdIR_holdsL','upper_core_insts','L_ex','transfer'],
 'coq/settheory/KQuotZFC.v':['Definition StandardZFC','KPrimeOrd_standardZFC_inconsistent','ac_reg_relcon','KPrimeOrd_ZFc_inconsistent'],
 'coq/settheory/KQuotZFTransfer.v':['K0_qtranslate_closed','K0_ZFc_inconsistent','KPrimeOrd_ZFc_inconsistent','K0_qZFc','K0_proves_empty'],
 'coq/settheory/KDecodeComplete.v':['KPrimeOrd_proves_decoded','KPrimeOrd_proves_disabled','KPrimeOrd_same_named','KPrimeOrd_distinct_named','decoded_core_derivations_equivalent'],
}

def main():
 p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,default=Path(__file__).resolve().parents[2]/'input/k230-rocq');p.add_argument('--out',type=Path,default=Path(__file__).resolve().parent/'k230_source_audit.json');a=p.parse_args()
 manifest=json.loads((a.repo/'manifest.json').read_text());files={f:h for f,h in manifest['local_files'].items()if f.endswith('.v')};require(len(files)==101,'unexpected local source count')
 code={};problems=[];hypotheses=[]
 pattern=re.compile(r'\b(?:Axiom|Axioms|Admitted|admit|Parameter|Parameters|Conjecture|native_cast_no_check|vm_cast_no_check|exact_no_check)\b|\bUnset\s+(?:Guard|Universe)\s+Checking\b')
 for file,expected in files.items():
  raw=(a.repo/file).read_bytes();require(hashlib.sha256(raw).hexdigest()==expected,'wrong source hash: '+file)
  txt=uncomment(raw.decode('utf-8'));code[file]=txt
  for m in pattern.finditer(txt):problems.append(dict(file=file,line=txt[:m.start()].count('\n')+1,token=m.group()))
  for m in re.finditer(r'\bHypothes(?:is|es)\s+([A-Za-z0-9_\']+)',txt):hypotheses.append(dict(file=file,line=txt[:m.start()].count('\n')+1,name=m.group(1)))
 require(not problems,'source-level trust escape found: '+str(problems))
 for file,terms in CHAIN.items():
  for term in terms:require(term in code[file],f'endpoint chain missing {term} in {file}')
 require(code['coq/tm/AuditCorrect.v'].count('Print Assumptions')==2,'wrong final assumption audit')
 require('Definition site_run\' := site_run box_mark box_inc box_dec0 box_decp.'in code['coq/tm/Sim230.v'],'runtime parameters not visibly instantiated')
 require('408419'in code['coq/tm/Boot230.v'],'missing exact bootstrap')
 report=dict(status='PASS_PINNED_LOCAL_SOURCE_ENDPOINT_AUDIT',local_sources=101,local_hashes_verified=101,upstream_sources_not_rebuilt=len(manifest['reference_files']),theorem_chain_identifiers=CHAIN,source_trust_escape_hits=problems,section_hypotheses=hypotheses,final_assumption_prints=2,runtime_box_parameters_instantiated_in='coq/tm/Sim230.v',rocq_rebuild=False,proof_scope='Literal source audit and mathematical theorem-chain inspection; no replacement for a clean build, kernel recheck, or compiled assumption dependency report.')
 a.out.write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:v for k,v in report.items()if k not in('theorem_chain_identifiers','section_hypotheses')},indent=2))

if __name__=='__main__':main()
