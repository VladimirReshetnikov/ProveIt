#!/usr/bin/env python3
"""Prepare P-factor two-provider union guard without invoking Lean."""
import hashlib
import json
import re
import shutil
from pathlib import Path

here = Path(__file__).resolve().parent
d = here.parents[1]
repo = next(p for p in here.parents if (p / 'lakefile.toml').is_file())
check = here.parent / 'current14-carrier65-diagonal-p-check'
srcdir = check / 'src/DiophantineConsistency'; srcdir.mkdir(parents=True, exist_ok=True)
src = srcdir / 'Current14Carrier65DiagonalP.lean'; shutil.copyfile(here / src.name, src)
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows = [{'module':'DiophantineConsistency.Current14Carrier65DiagonalP',
         'source':str(src.relative_to(repo)),'source_sha256':sha(src),
         'imports':re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)}]
manifest=check/'source-manifest.json';manifest.write_text(json.dumps({'rows':rows},indent=2)+'\n')
first=Path('/tmp/current14-carrier65-diagonal-rank-20261110')
second=Path('/tmp/current14-carrier65-diagonal-core-binding-retry-20261110')
s1=here.parent/'current14-carrier65-diagonal-rank-check/attempt01/state.json';o1=s1.parent/'outer-result.json'
a1=d/'reviews/current14-carrier65-diagonal-rank-terminal-independent/check.py'
s2=here.parent/'current14-carrier65-diagonal-core-binding-retry-check/attempt01/state.json';o2=s2.parent/'outer-result.json'
a2=d/'reviews/current14-carrier65-diagonal-core-binding-retry-terminal-independent/check.py'
old=(here.parent/'nine-sharing-sign17-lines-decoder-check/run.py').read_text()
old=old.replace('/tmp/nine-sharing-sign17-seed-lines-replay-20261110',str(first)).replace('/tmp/nine-sharing-sign17-lines-decoder-20261110','/tmp/current14-carrier65-diagonal-p-20261110')
start=old.index("STATE=D/'research/nine-sharing-sign17-seed-lines-replay-check/attempt01/state.json'")
end=old.index('\nroots=',start)
old=old[:start]+("STATE=D/'research/current14-carrier65-diagonal-rank-check/attempt01/state.json';"
                 "OUTER=STATE.parent/'outer-result.json';"
                 "AUDIT=D/'reviews/current14-carrier65-diagonal-rank-terminal-independent/check.py'")+old[end:]
old=re.sub(r"need\(sha\(STATE\)=='[0-9a-f]+'",f"need(sha(STATE)=='{sha(s1)}'",old)
old=re.sub(r"need\(sha\(OUTER\)=='[0-9a-f]+'",f"need(sha(OUTER)=='{sha(o1)}'",old)
old=re.sub(r"need\(sha\(AUDIT\)=='[0-9a-f]+'",f"need(sha(AUDIT)=='{sha(a1)}'",old)
old=old.replace("len(base['rows'])==1 and base['rows'][-1]['module']=='Sign17SeedLines'",
                "len(base['rows'])==2 and base['rows'][-1]['module']=='Current14Carrier65DiagonalRank'")
old=re.sub(r"need\(sha\(P/'source-manifest.json'\)=='[0-9a-f]+'",f"need(sha(P/'source-manifest.json')=='{sha(manifest)}'",old)
start=old.index("witness=D/'research/nine-sharing-sign17-k-ranking-witness/witness.json'")
end=old.index('base2=json.loads(STATE2.read_text())',start)
extra=f'''draft=D/'research/current14-carrier65-diagonal-p-draft/Current14Carrier65DiagonalP.lean'
need(sha(draft)=='{sha(here/src.name)}' and sha(P/'src/DiophantineConsistency/Current14Carrier65DiagonalP.lean')==sha(draft),'P source pin')
BASE2=Path({str(second)!r})
STATE2=D/'research/current14-carrier65-diagonal-core-binding-retry-check/attempt01/state.json';OUTER2=STATE2.parent/'outer-result.json'
need(sha(STATE2)=='{sha(s2)}','second provider state')
need(sha(OUTER2)=='{sha(o2)}' and json.loads(OUTER2.read_text())['outer_exit_code']==0,'second provider outer')
need(sha(D/'reviews/current14-carrier65-diagonal-core-binding-retry-terminal-independent/check.py')=='{sha(a2)}','second provider audit')
'''
old=old[:start]+extra+old[end:]
old=old.replace("len(base2['rows'])==1 and base2['rows'][-1]['module']=='Sign17ParamDecoder'",
                "len(base2['rows'])==2 and base2['rows'][-1]['module']=='Current14Carrier65DiagonalCoreBinding'")
needle="need(len(overlap)==1252 and all(firstmap[k]==secondmap[k] for k in overlap),'provider overlay mismatch')"
replacement="""exception='DiophantineConsistency/Current14Carrier65QFields.olean'
need(len(overlap)==1267 and exception in overlap,'provider overlap size')
need(all(firstmap[k]==secondmap[k] for k in overlap if k!=exception),'provider overlay mismatch')
need(firstmap[exception]!=secondmap[exception] and sha(firstmap[exception])==sha(secondmap[exception])=='ffc15e09467d94f0f1c8752c38fbb06579d16b30863fb8954ef0950b5a568f0b','QFields equal-byte route exception')"""
assert needle in old;old=old.replace(needle,replacement)
needle="if os.path.lexists(q):need(q.is_symlink() and str(q.resolve())==v,'union mismatch '+rel)"
replacement="if os.path.lexists(q):need(q.is_symlink() and (str(q.resolve())==v or (rel==exception and sha(q)==sha(v))),'union mismatch '+rel)"
assert needle in old;old=old.replace(needle,replacement)
old=old.replace('PASS decimal lines action cache and transition rows','PASS actual diagonal P degree')
old=old.replace('Audited single-context provider and direct source/object/guard observations; no Lean, complete transitive trace, global order or rank proof.',
                'Two audited providers; one explicitly pinned equal-byte QFields path difference; no Lean theorem or complete transitive trace.')
(check/'run.py').write_text(old)
print('Prepared diagonal P union guard; no Lean invoked.')
