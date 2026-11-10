#!/usr/bin/env python3
"""Independent Python byte comparison to manually inspected Lean mask recipes."""
import gzip,hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];sha=lambda b:hashlib.sha256(b).hexdigest();lean=root/'Lean/DiophantineConsistency/CurrentMaskData2011.lean';lowdef=root/'Lean/DiophantineConsistency/LowMaskData.lean';assert sha(lean.read_bytes())=='8e92c1f507bc250c31fb2671a921dfbef7a44ba643956f962cd64d9b50bd4582' and sha(lowdef.read_bytes())=='797ca9900ad6a1af0693aa241ad93f9e7679600f3fc7bee5d6acbddc61c9817b'
s=lean.read_text();l=lowdef.read_text()
for t in ('def radix : ℕ := 2 ^ 47','def beta : ℕ := radix ^ 2011 - 1','Finset.range 951 ∪ Finset.Ico 960 986 ∪ {1004}','def lowPort : ℕ := mask radix 2 2011 lowSupport','4 :: (List.replicate 916 8 ++ List.replicate 43 0 ++ List.replicate 9 1 ++','List.replicate 18 0 ++ List.replicate 8 1 ++ List.replicate 9 0 ++ [1, 2 ^ 45 - 4])','def highDigits : List ℕ := highPrefix ++ List.replicate 1005 0','def highPort : ℕ := Nat.ofDigits radix highDigits','![beta, K, lowPort, highPort + beta]'):assert t in s
assert 'B ^ len - 1 - (b-1) * supportValue B S' in l
# Independent digit-position construction: low mask digits are radix−2 at
# support positions and radix−1 elsewhere; high uses a direct power sum.
B=1<<47;support=set(range(951))|set(range(960,986))|{1004};assert len(support)==978
low=0
for j in reversed(range(2011)):low=low*B+(B-2 if j in support else B-1)
digits=[4]+[8]*916+[0]*43+[1]*9+[0]*18+[1]*8+[0]*9+[1,(1<<45)-4]+[0]*1005;assert len(digits)==2011
high=sum(d*(1<<(47*i)) for i,d in enumerate(digits) if d);beta=(1<<(47*2011))-1
seed=root/'research/nine-sharing-sign17-degree96-vdifference-candidate/seed.json';assert sha(seed.read_bytes())=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac';binding=json.loads(seed.read_text())['coefficient_binding'];out={}
for name,num in [('MC',low),('MF',high+beta)]:
 rec=binding['ports'][name];packed=(seed.parent/binding['path']/rec['file']).read_bytes();raw=gzip.decompress(packed);assert sha(packed)==rec['gzip_sha256'] and sha(raw)==rec['raw_sha256'] and len(raw)==rec['raw_bytes']==11815 and int.from_bytes(raw,'big')==num;out[name]={'gzip_sha256':sha(packed),'raw_sha256':sha(raw),'bytes':len(raw)}
print(json.dumps({'status':'PASS_EXTERNAL_INDEPENDENT','ports':out,'scope':'external Python byte comparison to manually transcribed source recipes; K0 excluded; no Lean file or port theorem'},indent=2,sort_keys=True))
