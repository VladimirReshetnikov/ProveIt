#!/usr/bin/env python3
"""Replay every recorded literal startup hit and check the whole source frame."""
from pathlib import Path
import json
from single_edits import table,lookup
HERE=Path(__file__).resolve().parent

def main():
 hits=[json.loads(x)for x in(HERE/'arbitrary_single_hits.jsonl').read_text().splitlines()]
 E=lookup(hit['j']for hit in hits);T=table();sites=json.loads((HERE/'pa194.sites.json').read_text())
 assert len(hits)==198 and len(E)==163
 ticks=0
 for hit in hits:
  rows=dict(T);key,act=E[hit['j']];rows[key]=act
  q=hit['start'];h=0;ones=set()
  for step in range(hit['steps']):
   w,d,q=rows[q,int(h in ones)];(ones.add if w else ones.discard)(h);h+=d
  ticks+=hit['steps']
  assert(q,h,sorted(ones))==(84,hit['head'],hit['ones'])
  expected={h-1,h+48+hit['gap']}
  expected.update(h+j for j,b in enumerate(sites[hit['site']][0])if b=='1')
  pos=h+49+hit['gap'];values=hit['values'];assert len(values)>=10 and hit['gap']>=0
  for value in values:assert value>=0;expected.update(range(pos+1,pos+value+2));pos+=value+2
  assert ones==expected
 print(json.dumps(dict(full_tape_hits=198,distinct_edits=163,replayed_transitions=ticks),indent=2))

if __name__=='__main__':
 if not __debug__:raise SystemExit('Assertions must be enabled')
 main()
