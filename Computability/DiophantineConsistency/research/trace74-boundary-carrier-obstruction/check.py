#!/usr/bin/env python3
"""Exact residue obstruction for the finite q=2 boundary seed."""
from pathlib import Path
from hashlib import sha256
import json, math, sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;G=H.parent/'trace74-mask-coordinate-probe/candidate.json'
raw=G.read_bytes();assert sha256(raw).hexdigest()=='dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353'
d=json.loads(raw);rows={r[0]:r for r in d['source']}
for row in [ ['P1mu2','*','bJ','XY'], ['LBt','*','V2','Bt'], ['center','-','n','LBt'],
 ['Hn','*','Hp','center'], ['lin','+','Hn','Kpos'], ['Zpart1','*','P1mu2','lin'],
 ['mu2inner','*','XY','Bt'], ['P1e','*','bJ','e'], ['brk','+','mu2inner','P1e'],
 ['Zpart2','*','Hp','brk'], ['Znum','-','Zpart1','Zpart2'], ['Mtot','*','P1mu2','Hp'] ]:
 assert rows[row[0]]==row,row
h,X,Y,c=1,14,8,58563
D=X*Y; A=X*Y+Y; H0=4*A-1; K=X*(3*c-2*X)+2
M=h*D*H0; rem=(h*D*K)%H0
assert (D,H0,K,M,rem)==(112,479,2459256,53648,176)
assert math.gcd(D,H0)==1 and K%H0==70 and rem!=0
# Exact row identities give Z=hD*(H(n−V² B)+K)−H*(DB+h e).
# Every term except hD*K is a multiple of H, for all integer B,e,n,V.
# M is a multiple of H, so a nonzero residue proves M does not divide Z.
print(json.dumps({'status':'PASS','candidate_sha256':sha256(raw).hexdigest(),'h':h,'D':D,'H':H0,'K':K,'M':M,'K_mod_H':K%H0,'Z_mod_H_for_all_remaining_registers':rem,'gcd_D_H':math.gcd(D,H0),'conclusion':'M does not divide Z for any remaining integer register values at this seed','scope':'exact conditional carrier residue; no claim that 74 zero implies M divides Z in this boundary chart'},sort_keys=True))
