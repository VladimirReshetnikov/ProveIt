#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-prefix-rank-composition-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'17847dda236f7d2ec70d9df5eb518aad631d19330829cf5869de76b681bff672','source-manifest.json':'add314a89682579f31a334d6db41dab5b7ee45ecd8cccee73b6216426bdc016b','bpower-survey.py':'ffc70e20f1e739d7d596148c4857f8ada5c2c8078d3c04eeb3477ae601789268','src/DiophantineConsistency/Sign33MacroRankComposition.lean':'c8ed91d6c2d11b555cc5c18be76af283a3583be919806ce75c57216c47add090'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==1 and m[0]['imports']==['DiophantineConsistency.Sign33MacroRankCodeLink','DiophantineConsistency.Sign33MacroPrefixBPower'];s=(P/'src/DiophantineConsistency/Sign33MacroRankComposition.lean').read_text();old=D/'research/nine-seed38-jones-prefix-rank-composition-retry01/src/DiophantineConsistency/Norm38MacroRankComposition.lean';assert s==old.read_text().replace('Norm38','Sign33')
head=s.split('theorem d11_rankCode',1)[1].split(':= by',1)[0];assert 'd11.values a (Fin.last 10)' in head and [int(x) for x in re.findall(r'd10.values a ⟨(\d), by decide⟩',head)]==[0,4,7,5,3,2,8,6]
for x in ['rw [d11_rank_raw]','rw [d10_B_eq_b_pow, rankRaw_eq_rankCode]','((Fin.last 0)'+'.castSucc'*9+' : Fin 10) = ⟨0, by decide⟩'] :assert x in s
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'proposed d11 rankCode in symbolic d10 prefix entries only'},sort_keys=True,indent=2))
