#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2]; P=D/'research/nine-sharing-sign31-seed-squares-check'
pins={'run.py':'c23513b8d8b1257d87335f36fce98155caba6680577ea572c5ecda9fe1739f10','source-manifest.json':'6e95830840784b5ac086b7809473a8f02ca94afe3f555b01f6a869ca565f4890','src/DiophantineConsistency/SharingSeed31Sextic.lean':'52e887de8cc5197d0c7ad8543f9e1b3f51f42a20302475b83df342693d8469c1','src/DiophantineConsistency/SharingSign31Squares.lean':'fce14ad3fad096ea22ae58f7fdf50f2e4860c408c4c2389096516b02c73bca1f'}
for n,h in pins.items(): assert hashlib.sha256((P/n).read_bytes()).hexdigest()==h,n
s=(P/'src/DiophantineConsistency/SharingSign31Squares.lean').read_text(); assert 'SharingSign33Squares.squareSum_zero_iff' in s and 'SharingSign33Squares.square_syntax' in s and '#print axioms DiophantineConsistency.SharingSign31Squares.seed_zero_iff_residuals' in s
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],cwd=D,text=True,capture_output=True); assert r.returncode==0,(r.returncode,r.stdout,r.stderr); d=json.loads(r.stdout); assert d['status']=='PASS_NO_LEAN_PREFLIGHT' and d['stage_count']==2
print(json.dumps({'status':'PASS','preflight_exit':r.returncode,'source_pins':len(pins),'scope':'Source and point-in-time provider prelaunch; no Lean replay or transitive trace.'},sort_keys=True))
