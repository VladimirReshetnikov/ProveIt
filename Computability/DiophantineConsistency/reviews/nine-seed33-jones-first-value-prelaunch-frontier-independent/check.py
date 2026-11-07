#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-first-value-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'ee82a6791e8b5ca4379d791047f6b50d376495af98e92c5febc9ca173f9847bf','source-manifest.json':'517afe3a2f17f807c87782fa8fb73716ce0bf8d6a357b05692291be80871d498','cuts-survey.py':'b558ba53a1a449764e1ef3a10b8d4a16d31b9f9e45b9e54f59d31ff1b840b616'}.items():assert sha(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==1 and m[0]['module']=='DiophantineConsistency.Sign33MacroPrefixFirst' and m[0]['imports']==['DiophantineConsistency.Sign33MacroPrefixes','DiophantineConsistency.Sign33MacroCuts'];p=P/'src/DiophantineConsistency/Sign33MacroPrefixFirst.lean';s=p.read_text();assert sha(p)==m[0]['source_sha256']=='d47d077244dbb46ebc3a63256196118da254693ed6ac0e42319b5eecc4ab2072'
d=(D/'research/nine-seed33-jones-named-prefix-check/src/DiophantineConsistency/Sign33MacroPrefixes.lean').read_text();assert 'def d1 : Dag 1 := .snoc d0 (.add (.add (.fixedY) (.constant (1 : Int))) (.input ⟨0, by decide⟩))' in d
for x in ('d1.values a (Fin.last 0)','indexY Sign33MacroLanguage.seed 0','((1 : Int) : R)','a ⟨0, by decide⟩','rw [d1, Sign33MacroCuts.snoc_last]','  rfl'):assert x in s
print(json.dumps({'status':'PASS_STATIC','scope':'proposed first short-prefix value only; no full recipe or semantic equality'}))
