#!/usr/bin/env python3
"""Fresh metadata and scalar checks only; no supplied verifier is executed."""
import argparse,hashlib,io,json,subprocess,zipfile
from fractions import Fraction
from pathlib import Path
REPO=Path('/home/codex/.codex/worktrees/2a71/Proofs')
COMMIT='26e036956381b07bb43de0187965f8dcdf9194fb'
ARCHIVE='docs/incoming/hat_randomness_frontier.zip'
MEMBER='hat_randomness_frontier/hat_randomness_frontier.tex'
ARCHIVE_SHA='eccc49ac838592997e1c7d8ef0c5ba7c1a95bd76abbb8f12814f552dc34b9e20'
PRIOR={'md':'55d864059205571c3eeab0d7522c72eaf7ea064c692fa9672dd10a7adc8b0a37','json':'9958f93dc6e3a807adc09829cee77b804d08818441ddd0f0abe50ea0a707f91c','py':'6156d71193d185cfcc285dec4227139e49ed7d5a9a53d5bc11609599f8b4c562'}
def need(v,m):
 if not v:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=REPO)
def fraction(f):return str(f.numerator)+'/'+str(f.denominator)
def build():
 raw=git('show',COMMIT+':'+ARCHIVE);need(sha(raw)==ARCHIVE_SHA,'archive pin');z=zipfile.ZipFile(io.BytesIO(raw));tex=z.read(MEMBER);lines=tex.decode().splitlines();spans=[]
 for a,b,role in [(193,262,'model and fairness, reexamined interface'),(263,469,'new covariance, projection and zero-query dependencies'),(470,680,'new complete Fourier and aggregate-cost argument'),(681,822,'reexamined stopped-process/private/finite-public proofs')]:
  span=('\n'.join(lines[a-1:b])+'\n').encode();spans.append({'first_line':a,'last_line':b,'normalized_utf8_sha256':sha(span),'role':role})
 pins={}
 for ext,pin in PRIOR.items():
  p=Path('/tmp/review_new_actions_26e036956.'+ext)
  if not p.exists():p=REPO/'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'/('review_new_actions_26e036956.'+ext)
  b=p.read_bytes();need(sha(b)==pin,'prior review pin');pins[ext]={'sha256':pin,'bytes':len(b)}
 constants={'d2_spectral_denominator':4*3**4,'aggregate_denominator':4*3**4*4**2,'variance_at_least_6K_denominator':4*3**4*4**2*4,'hypercontractive_induction_slack_b4':fraction(Fraction(1)-Fraction(1,9))}
 need(constants['aggregate_denominator']==5184 and constants['variance_at_least_6K_denominator']==20736,'bound constants')
 means=0;paths=0
 for i in range(1,129):
  tail=Fraction(1,i+1);mean=(1-tail)*Fraction(i+1,i);need(mean==1,'correlated scalar marginal cost');means+=1
 for t in range(33):
  for N in range(65):
   direct=sum((Fraction(0) if i<=t else Fraction(i+1,i))-1 for i in range(1,N+1))
   expected=-min(N,t)+sum((Fraction(1,i) for i in range(t+1,N+1)),Fraction(0))
   need(direct==expected,'scalar path excess identity');paths+=1
 covariance=Fraction(1,2)*2*Fraction(3,2)-1;need(covariance==Fraction(1,2),'nonindependence witness')
 return {'schema':'bounded-hat-endpoint-proof-review-v1','reviewer_sha256':sha(Path(__file__).read_bytes()),'archive':{'commit':COMMIT,'path':ARCHIVE,'blob':git('rev-parse',COMMIT+':'+ARCHIVE).decode().strip(),'bytes':len(raw),'sha256':sha(raw)},
 'member':{'path':MEMBER,'bytes':len(tex),'sha256':sha(tex),'utf8_lines':len(lines),'human_read_spans':spans},'prior_review':pins,
 'scalar_checks':{'constants':constants,'correlated_cost_model':{'law':'P(T=t)=1/((t+1)(t+2)), t>=0','cost':'c_i=0 if T>=i; c_i=(i+1)/i otherwise','expectation_checks':means,'finite_path_identities':paths,'covariance_c1_c2':fraction(covariance),'not_a_hat_strategy':True}},
 'assessment':{'new_proof_lines':[263,680],'new_proof_line_count':418,'all_endpoint_dependency_lines':[193,822],'endpoint_dependency_line_count':630,'mathematical_finding':None,'private_positive_probability_zero_claim':False,'finite_public_conditional_caps_assumed':False,'gate_cost_claim':False},
 'execution_scope':{'supplied_or_predecessor_program_execution':False,'prior_collectors_executed':False,'archive_builds':False,'external_source_audit':False,'full_article_review':False,'repository_mutations':False}}
def main():
 ap=argparse.ArgumentParser();g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output');g.add_argument('--expect');args=ap.parse_args();d=build();raw=(json.dumps(d,indent=2,sort_keys=True)+'\n').encode()
 if args.output:
  with open(args.output,'xb') as f:f.write(raw)
 else:need(raw==Path(args.expect).read_bytes(),'receipt replay')
 print(json.dumps({'status':'PASS','new_proof_lines':418,'dependency_lines':630,'scalar_mean_checks':128,'scalar_path_checks':2145}))
if __name__=='__main__':main()
