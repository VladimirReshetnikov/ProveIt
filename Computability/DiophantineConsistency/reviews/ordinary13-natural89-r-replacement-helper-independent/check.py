#!/usr/bin/env python3
"""Pinned helper interfaces and independent finite signed-root controls."""
from pathlib import Path
import hashlib,itertools,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
pins=json.loads((HERE/'pins.json').read_text())
for f,h in pins.items():assert hashlib.sha256((ROOT/f).read_bytes()).hexdigest()==h,f
s=(ROOT/'research/ordinary13-natural89-r-replacement-model-draft/Natural89RReplacement.lean.src').read_text()
for x in ['have he8 : e 8=0','EtaNaturalJPositiveDraft.J_positive p e hz85',
 'ResidueCompactQBoundDraft.beta_at_least_46','have he9 : 0<e 9',
 'have he10 : (1:V)≤e 10+1','have hk : (2:V)≤k e',
 'EtaNaturalGapRankDraft.first_norm p e hz85']:
 assert x in s,x
assert 'ResidueRootSwitchExtractDraft.positive_replacement\n      (e 0*(p 0:V)) (m p e*k e) (k e) (Bt p e) (firstRoot p e) hb hk hform hnorm\'' in s
extract=(ROOT/'research/ordinary13-residue-root-switch-extraction-draft/ResidueRootSwitchExtract.lean.src').read_text()
for x in ['(hb : 0<b) (hk : 2≤k)','ReducedNormSigned.natural_magnitude_square',
 'ArithmeticAdaptiveQuotients2011.scaled_quotient','Trace75IntegralTransport.natural_dvd_of_signed',
 'ResidueRootSwitchArithmeticDraft.switch_from_zero']:
 assert x in extract,x
count=solutions=0
for b,ell,k,t in itertools.product(range(1,9),range(26),range(2,13),range(1,13)):
 P=b*t; z=b*(ell+k-k*P)-P; target=b*b*(1+ell*(ell+k))
 assert (ell+k)**2-(1+ell*(ell+k))==ell*k+k*k-1>0
 if z*z==target:
  assert z<0 and (-z)%b==0
  tau=-z//b;assert tau>ell and tau*tau==1+ell*(ell+k)
  new=z+2*b*tau;assert new==-z and new*new==z*z
  solutions+=1
 count+=1
# Counterexample to weakening the helper's k≥2 under ell merely natural.
b,ell,k,P=1,0,1,0;z=b*(ell+k-k*P)-P
assert z>0 and z*z==b*b*(1+ell*(ell+k))
# Helper also permits ell=0 at k=2: first root flips with tau=1.
b,ell,k,P,tau=1,0,2,1,1;z=b*(ell+k-k*P)-P
assert z==-b*tau and z*z==b*b*(1+ell*(ell+k)) and z+2*b*tau==-z
print(json.dumps({'source_pins':pins,'signed_root_controls':count,'conditional_root_solutions':solutions,
 'k1_fact_level_counterexample':True,'ell_zero_k2_valid':True,'lean_executed':False,
 'scope':'helper and k-bound review; graph preservation handled separately; no model proof'},sort_keys=True,indent=2))
