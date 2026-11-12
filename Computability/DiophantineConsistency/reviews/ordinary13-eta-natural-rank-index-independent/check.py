#!/usr/bin/env python3
"""Independent natural-rank and early-index interface review; no Lean."""
from pathlib import Path
import hashlib,json,random,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent;root=here.parents[1]
pins={
'research/ordinary13-eta-natural-rank-index-model-draft/EtaNaturalRankIndex.lean.src':'0832b087042375be828531a61d8baeca8676e64d386f6995e1f12de3bf441c41',
'research/ordinary13-eta-natural-rank-index-model-draft/README.md':'c476bd0d78d4b752fae424d7da35466055a0aa972260cfa9ee7f9cea98cf9d8e',
'research/ordinary13-eta-natural-gap-rank-model-draft/EtaNaturalGapRank.lean.src':'6b38dc7c935520220392e6d1b89e36655ef175bbaec9a4d60501adce8a93f863',
'research/ordinary13-eta-natural-X-positive-model-draft/EtaNaturalXPositive.lean.src':'e3bace196b09c86927bd178c279111ab4c97d076a18711c676ff127f002fe063',
'research/ordinary13-residue-compact-qbound-model-draft/ResidueCompactQBound.lean.src':'79fb9cc240fa5f24c4a89bbce7c10773e2986c53b677320514009fe964bf622c',
'research/ordinary13-eta-zero-early-congruence-model-draft/EtaZeroEarlyCongruence.lean.src':'7cb45a1766cedf64f1ad6f1a11977ec66990a9c7977f41a9e100a6d36742845e',
'research/ordinary13-eta-zero-index-parity-contradiction-draft/EtaZeroIndexParity.lean.src':'a5aac5250b0b4c05fa765ed1013e5287706f038ea60e5083d9c4cba4025e0e74',
'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json':'97273735d1537b597544604d19969630c8464469e9a3ab2f8825f52dc602a648'}
s={}
for p,h in pins.items():
 b=(root/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[p]=b.decode()
d=s['research/ordinary13-eta-natural-rank-index-model-draft/EtaNaturalRankIndex.lean.src']
for t in ['theorem rank_at_least_26','(hq : 6≤q p v)','theorem compact_rank_at_least_26',
 'ResidueCompactQBoundDraft.compact_q_at_least_47 K v hJ','theorem compact_early_index_of_norms',
 '(hfirst :','(hmain :','EtaNaturalXPositiveDraft.X_positive p v hz hbeta',
 'EtaNaturalGapRankDraft.compact_rank_window K v hz',
 '(Y p v) (k v) (rank p v) (v 9) (v 12) (v 7+1) tau',
 'hR24 hwindow hfirst hmain']:
 assert t in d,t
b=s['research/ordinary13-residue-compact-qbound-model-draft/ResidueCompactQBound.lean.src']
assert '''theorem compact_q_at_least_47 (K : ℕ) (v : Fin 13 → V)
    (hJ : 0<v 0) : (47:V)≤q (ports K) v''' in b
e=s['research/ordinary13-eta-zero-early-congruence-model-draft/EtaZeroEarlyCongruence.lean.src']
assert '''theorem early_index_of_actual_carrier (q X Y k R eta gamma s tau : V)
    (hq : 0<q) (hX : 0<X) (hY : Y=q^3*s) (hY8 : 8≤Y) (hk : 0<k)
    (hR24 : 24≤R) (hwindow : R+q^3+q+1≤q^4)''' in e
for left,right in [('xcoord n (2*(X*Y*Y-1)+1)=tau','xcoord n (2*(X p v*Y p v*Y p v-1)+1)=tau'),
 ('2*ycoord n (2*(X*Y*Y-1)+1)=k','2*ycoord n (2*(X p v*Y p v*Y p v-1)+1)=k v'),
 ('k=2*n+4*(X*Y*Y)*w','k v=2*n+4*(X p v*Y p v*Y p v)*w')]:
 assert left in e and right in d,(left,right)
assert '(hR26 : 26 ≤ R)' in s['research/ordinary13-eta-zero-index-parity-contradiction-draft/EtaZeroIndexParity.lean.src']
g=json.loads(s['research/ordinary13-eta-zero-graph-adapter-audit/prototype.json']);rows={r[0]:r for r in g['source']}
for row in [['alpha','+','n_alpha',1],['q','+',1,'qm'],['G','+','alpha','g44'],['R','+','g47','g50']]:assert rows[row[0]]==row
# Natural truncated rank is bounded even when the signed rank is different.
assert ((5-1)*max(5-5,0)+1)*(5*5-1)==24
q,beta,J,F,alpha=6,5,1,7,1
nat=((q-1)*max(q-F,0)+alpha)*(q*q-1)
signed=((q-1)*(q-F)+alpha)*(q*q-1)
assert q==1+beta*J and nat==35 and signed==-140
rng=random.Random(614070);nogap=0
for _ in range(5000):
 q=rng.randrange(6,100);F=rng.randrange(1,150);alpha=rng.randrange(1,25);J,MC,MF=(rng.randrange(0,30) for j in range(3))
 A=(q-1)*max(q-F,0)+alpha;R=A*(q*q-1)+(MC+q*MF)*J
 assert A>=1 and q*q-1>=35 and R>=26
 nogap+=F+alpha>=q
assert nogap>0
print(json.dumps({'source_sha256':pins,'natural_rank_controls':5000,'controls_without_gap':nogap,'q5_rank24_control':True,'q6_signed_natural_discrepancy_control':True,'lean_executed':False,'scope':'conditional source interfaces and bounded rank controls; no Lean, graph-zero extraction, port provenance or iPRA endpoint'},sort_keys=True,indent=2))
