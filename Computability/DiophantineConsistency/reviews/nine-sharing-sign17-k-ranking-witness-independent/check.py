#!/usr/bin/env python3
"""Independently reconstruct external witness from Lean table source, no Lean execution."""
import hashlib,json,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
table=root/'Lean/DiophantineConsistency/WangTiles942TableData.lean';data=root/'Lean/DiophantineConsistency/WangTiles942Data.lean';inv=root/'Lean/DiophantineConsistency/MFWangTiles942Permutation.lean';wpath=root/'research/nine-sharing-sign17-k-ranking-witness/witness.json';gen=root/'research/nine-sharing-sign17-k-ranking-witness/build.py';coeff=root/'research/padding-staircase-independent/coefficients.json'
for p,h in [(table,'0d2bf996f4e7e19acba82d5d3f1805a71c17cb1a9bcdc959e67453da14697a2c'),(data,'afea682c7a961f9cc30015be3d12469835a6ace52e9104b054c7ccb6d182d9de'),(inv,'84b439157b29b721853a544bfc3083207bc6195e0b8357c7744ddfd89e7c4093'),(wpath,'7f50654d30197158157533857892ddde91b7234bfdfe0cc6089282e5613b81a3'),(gen,'56bfcc1176973e6fade3630b2bd317c0c293aef7644c0c5e5a40a1b36d0e0daf'),(coeff,'43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93')]:assert sha(p)==h
s=data.read_text(); block=s.split('def actionCache : Array Action := #[',1)[1].split(']',1)[0]; actions=[(a=='true',b=='true',int(c)) for a,b,c in re.findall(r'\((true|false), (true|false), (\d+)\)',block)];assert len(actions)==430
part=s.split('def targetList (d : Bool) : List ℕ :=',1)[1].split('def targets',1)[0]; mt=re.search(r'if d then (\[[^]]*\]) else (\[[^]]*\])',part);assert mt;targets={True:json.loads(mt[1]),False:json.loads(mt[2])};assert all(targets[d]==sorted({q for _,dd,q in actions if dd==d}) for d in (False,True))
def rail(d,q):return 205-199*int(d)+sum(v<q for v in targets[d])
# Transcription of orderedRows and its constructor families from the pinned Lean table.
ordered=[(0,(2,435,3,1))]
for j,(bit,d,q) in enumerate(actions):ordered.append((j+1,((1-int(d))*rail(False,q),j+2,int(d)*rail(True,q),int(bit))))
for a in (1,0):
 for b in range(2):ordered.append((433-2*a+b,(0,432*a+b,0,432*a+b)))
for d in (True,False):
 for q in targets[d]:
  for b in range(2):ordered.append((423+2*rail(d,q)+b,(int(d)*rail(d,q),b,(1-int(d))*rail(d,q),2*q+b+2)))
for a in range(2):
 for b in range(2):ordered.append((923+2*a+b,(0,432*a+b,0,438)))
ordered.extend([(927,(2,434,2,0)),(928,(3,436,4,4)),(929,(4,436,4,0))]);ordered.extend((496+t,(1,438,1,t)) for t in (434,435,436));ordered.extend((933+3*a+b,(a*a,437,b,437)) for a in range(3) for b in range(3))
assert [i for i,t in ordered]==list(range(942)) and len({t for i,t in ordered})==942
weight=lambda t:1+1024*(1+t[0]+256*t[1]+131072*t[2]+33554432*t[3]);w=json.loads(wpath.read_text());rows=w['rows'];values=json.loads(coeff.read_text());assert w['count']==len(rows)==942 and [r['physical'] for r in rows]==list(range(942)) and [r['index'] for r in rows][0]==0 and sorted(r['index'] for r in rows)==list(range(942))
for r in rows:
 tile=ordered[r['index']][1];assert tuple(r['tile'])==tile and r['weight']==weight(tile) and 2*r['weight']==values[r['physical']]
assert all(rows[i]['weight']>rows[i+1]['weight'] for i in range(1,941));assert all(r['physical']==(0 if r['index']==0 else 1+sum((2**44-1+weight(t)-r['weight'])//2**44 for _,t in ordered[1:])) for r in rows)
print(json.dumps({'status':'PASS_EXTERNAL_RECONSTRUCTION','count':942,'scope':'Python reconstruction of pinned Lean table and ranking formulas, not a Lean evaluation or file theorem'},indent=2))
