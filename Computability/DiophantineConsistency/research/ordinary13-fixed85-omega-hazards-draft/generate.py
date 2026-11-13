from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-fixed85-omega-hazards-draft')
pins=json.loads((D/'source-pins.json').read_text())
for p,h in pins.items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
fix={}
q3old='  have hq3 : 3≤q p v := by omega'
q3new='''  have hq3 : 3≤q p v := by
    have h2 : (2:V)≤(v 1+1)+(v 2+1) := by
      have hh := add_le_add hF ha
      simpa only [show (1:V)+1=2 by ring] using hh
    have hh : (2:V)<q p v := lt_of_le_of_lt h2 hgap
    simpa only [show (2:V)+1=3 by ring] using lt_iff_succ_le.mp hh'''
for n in ['ResidueExactIndexModel','ResidueExactIndexWitness']:fix[n]=[(q3old,q3new)]
fix['Residue90CompactGraphGamma']=[('''  have hq2 : 2≤q p v := by
    have h := pos_iff_one_le.mp hb
    dsimp [q]
    omega''','''  have hq2 : 2≤q p v := by
    have hh := add_le_add_left (pos_iff_one_le.mp hb) (1:V)
    simpa only [q,show (1:V)+1=2 by ring] using hh''')]
fix['Residue90FirstNormGap']=[('''  have hk2 : (2:V)≤k v := by
    have h9 := Arithmetic.zero_le (v 9)
    have h10 := Arithmetic.zero_le (v 10)
    dsimp only [k]
    omega''','''  have hk2 : (2:V)≤k v := by
    have h9 : (1:V)≤v 9+1 := by simp
    have h10 : (1:V)≤v 10+1 := by simp
    have hh := add_le_add h9 h10
    simpa only [k,show (1:V)+1=2 by ring] using hh''')]
fix['Residue90FyForce']=[('''  dsimp only [c]
  omega''','''  have hh := add_le_add he hk'
  simpa only [c,show (1:V)+1=2 by ring] using hh''')]
fix['Residue90GammaModel']=[('''      have hq3nonneg := Arithmetic.zero_le (q^3)
      have hqnonneg := Arithmetic.zero_le q
      omega''','''      have h : R≤R+(q^3+q) := le_add_of_nonneg_right (Arithmetic.zero_le (q^3+q))
      have hh := add_le_add_right h (1:V)
      simpa only [add_assoc] using hh''')]
fix['AQ17Forced105Arithmetic']=[('''  simp [hz] at h
  omega''','''  simp [hz] at h
  have hlt : q*(y*y)<1+q*(y*y) := lt_add_of_pos_left _ (by simp)
  rw [←h] at hlt
  exact (not_lt_of_ge hy) hlt'''),('''    have hfour : (4:V)≤q*(z*z) := by simpa using hm
    omega''','''    have hfour : (4:V)≤q*(z*z) := by simpa using hm
    have hbad : (4:V)≤1 := by simpa only [he] using hfour
    exact (not_lt_of_ge hbad) (by norm_num : (1:V)<4)''')]
fix['ResidueRankLower']=[('''  have hq3 : (3:V)≤q := by omega''','''  have hq3 : (3:V)≤q := by
    have h2 : (2:V)≤F+alpha := by
      have hh := add_le_add hF1 ha1
      simpa only [show (1:V)+1=2 by ring] using hh
    have hh : (2:V)<q := lt_of_le_of_lt h2 hgap
    simpa only [show (2:V)+1=3 by ring] using lt_iff_succ_le.mp hh'''),('''  have hqm2 : (2:V)≤q-1 := by omega''','''  have hqm2 : (2:V)≤q-1 := by
    apply (add_le_add_iff_right (1:V)).mp
    rw [hqminus]
    simpa only [show (2:V)+1=3 by ring] using hq3'''),('''  have hqF2 : (2:V)≤q-F := by omega''','''  have hqF2 : (2:V)≤q-F := by
    have hh : (1:V)<q-F := lt_of_le_of_lt ha1 haF
    simpa only [show (1:V)+1=2 by ring] using lt_iff_succ_le.mp hh'''),('''  have h5 : (5:V)≤(q-1)*(q-F)+alpha := by omega''','''  have h5 : (5:V)≤(q-1)*(q-F)+alpha := by
    have hh := add_le_add h4 ha1
    simpa only [show (4:V)+1=5 by ring] using hh'''),('''  have h8 : (8:V)≤q*q-1 := by omega''','''  have h8 : (8:V)≤q*q-1 := by
    apply (add_le_add_iff_right (1:V)).mp
    rw [hq2minus]
    simpa only [show (8:V)+1=9 by ring] using hq2''')]
for name,replacements in fix.items():
    match=[p for p in pins if Path(p).name==name+'.lean.src']
    assert len(match)==1,name
    s=Path(match[0]).read_text()
    for old,new in replacements:
        assert s.count(old)==1,(name,old)
        s=s.replace(old,new)
    for imp in ['Mathlib.Tactic.NormNum','Mathlib.Tactic.Ring']:
        line='import '+imp+'\n'
        if line not in s:s=line+s
    out=D/(name+'Repaired.lean.src')
    if sys.argv[1:]==['--check']:
        assert out.read_text()==s,name
    else:
        assert not sys.argv[1:]
        out.write_text(s)
