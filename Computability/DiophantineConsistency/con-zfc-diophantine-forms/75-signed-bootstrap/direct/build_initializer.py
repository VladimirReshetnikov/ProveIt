#!/usr/bin/env python3
"""Generic finite-input Wang front end; no arithmetic tuple or universality claim."""
from pathlib import Path
import json

def build(n,s,actions,word):
    assert word and all(0<=a<s for a in word)
    assert len(actions)==n*s
    assert all(0<=v<s and direction in ('L','R') and 0<=target<=n
               for v,direction,target in actions)
    head=lambda q,a:f'head:{q}:{a}'
    sym=lambda a:f'symbol:{a}'
    SR=sorted({t for v,d,t in actions if d=='R'})
    SL=sorted({t for v,d,t in actions if d=='L'})
    tiles=[]
    for q in range(n):
      for a in range(s):
        v,d,t=actions[q*s+a]
        tiles.append(('O',head(q,a),'right:'+str(t),sym(v)) if d=='R'
                     else ('left:'+str(t),head(q,a),'O',sym(v)))
    for a in range(s):
      tiles += [('O',head(n,a),'O',head(n,a)),('O',sym(a),'O',sym(a)),
                ('O',sym(a),'O','H'),('O',head(n,a),'O','H')]
      for q in SR: tiles.append(('right:'+str(q),sym(a),'O',head(q,a)))
      for q in SL: tiles.append(('O',sym(a),'left:'+str(q),head(q,a)))
    first=lambda a:('L','I','D',head(0,a))
    data=lambda a:('D','I','D',sym(a))
    start=('D','Q','R',sym(0))
    bad=('BAD',sym(0),'O',sym(0))
    tiles += [('L','I','L',sym(0)),('R','I','R',sym(0)),start]
    tiles += [first(a) for a in range(s)]+[data(a) for a in range(s)]
    tiles += [('HB','H','HB','I'),('HB','H','HB','Q')]
    tiles += [(a,'V',b,'V') for a in ('O','HB','R') for b in ('O','HB','L')]
    tiles += [bad]
    assert len(tiles)==len(set(tiles))
    assert len(tiles)==n*s+s*(len(SR)+len(SL))+6*s+15
    ordered=[start,bad]+sorted(set(tiles)-{start,bad})
    prefix=[start]+[data(a) for a in word[:0:-1]]+[first(word[0])]
    return {'scope':'Generic Wang front end only. This fixture is NOT a ZFC refuter.',
            'working_states':n,'symbols':s,'actions':actions,'input_word':word,
            'tile_count':len(ordered),'tiles':ordered,
            'right_to_left_prefix_tile_ids':[ordered.index(t) for t in prefix],
            'prefix_length':len(prefix)}

if __name__=='__main__':
    fixture=build(1,2,[(0,'R',1),(1,'R',1)],[1,0])
    assert fixture['tile_count']==31
    assert fixture['prefix_length']==3
    Path(__file__).with_name('TOY_INITIALIZER.json').write_text(json.dumps(fixture,indent=2)+'\n')
    print('31 distinct tiles; 3 fixed prefix positions; generic count identity verified.')
