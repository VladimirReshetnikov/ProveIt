#!/usr/bin/env python3
"""Independent audit: reads JSON only; imports neither compiler nor upstream code."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
packet=json.loads((ROOT/'data/semigroup.json').read_text())
I=(1,0,0,1)
T=(1,2,0,1)

def check(test, message):
    if not test:
        raise AssertionError(message)

def mul(a,b):
    p,q,r,s=a; u,v,w,x=b
    return p*u+q*w,p*v+q*x,r*u+s*w,r*v+s*x

def inverse(a):
    p,q,r,s=a
    check(p*s-q*r==1,'determinant')
    return s,-q,-r,p

def shear_conjugate(j):
    # Literal powers of Q and independently multiplied conjugation.
    return mul(mul((1,0,-2*j,1),T),(1,0,2*j,1))

codes={a:i+1 for i,a in enumerate('01ABCDEFGHIJKLMNO[]X#')}
check(packet['top_codes']==codes,'code alphabet')

def phi(w):
    out=I
    for a in w:
        out=mul(out,shear_conjugate(codes[a]))
    return out

def blocks(matrix):
    check(len(matrix)==4 and all(len(r)==4 for r in matrix),'shape')
    check(all(matrix[i][j]==0 for i in range(4) for j in range(4) if (i<2)!=(j<2)),'off-diagonal block')
    return tuple(matrix[i][j] for i in range(2) for j in range(2)),tuple(matrix[i][j] for i in range(2,4) for j in range(2,4))

G={g['name']:blocks(g['matrix']) for g in packet['generators']}
tiles={t['id']:t for t in packet['tiles']}
rules={r['id']:r for r in packet['rules']}
check(len(G)==len(set(G.values()))==229,'generator census')
check(len(tiles)==114 and len(rules)==93,'tile/rule census')
check(len(packet['alphabet'])==20,'alphabet census')
for i,a in enumerate('01ABCDEFGHIJKLMNO[]X',1):
    check(tiles[i]['kind']=='copy' and tiles[i]['h']==tiles[i]['g']==a,'copy tile inventory')
for rid,rule in rules.items():
    tile=tiles[rid+20]
    check(tile['kind']=='rewrite' and tile['rule_id']==rid and (tile['h'],tile['g'])==(rule['rhs'],rule['lhs']),'rewrite tile inventory')
check(tiles[114]['kind']=='separator' and tiles[114]['h']==tiles[114]['g']=='#','separator inventory')
# Independent rule inventory from the pinned transition DATA, using explicit
# standard head-before-scanned-cell local successor templates.
table=json.loads((ROOT/'data/u15_table.json').read_text())
expected=set()
for cell,row in table.items():
    if row is None:
        check(cell=='J1','unique halting transition')
        continue
    state,read=cell
    written,direction,next_state=row
    written=str(written)
    if direction=='R':
        expected.update((state+read+c,written+next_state+c) for c in '01')
        expected.add((state+read+']',written+next_state+'0]'))
    else:
        check(direction=='L','movement direction')
        expected.update((c+state+read,next_state+c+written) for c in '01')
        expected.add(('['+state+read,'['+next_state+'0'+written))
expected.update({('J1','X'),('0X','X'),('1X','X'),('X0','X'),('X1','X'),('[X]','X')})
check(len(expected)==93 and expected=={(r['lhs'],r['rhs']) for r in rules.values()},'entire directed rule inventory')
for i,tile in tiles.items():
    x=shear_conjugate(i)
    check(G['A'+str(i)]==(phi(tile['h']),x),'A numerical formula')
    check(G['B'+str(i)]==(inverse(phi(tile['g'])),mul(mul(inverse(T),inverse(x)),T)),'B numerical formula')
    check(tile['h'] and tile['g'],'nonerasing tiles')
check(G['C']==(inverse(phi('X#')),T),'C numerical formula')
for top,bottom in G.values():
    inverse(top); inverse(bottom)

# Check the finite semigroup ledger directly from the integer packet.
entries=[v for g in packet['generators'] for row in g['matrix'] for v in row]
ledger=packet['ledger']
check(max(map(abs,entries))==ledger['maximum_absolute_generator_entry']==63038000,'maximum entry')
check(sum(v!=0 for v in entries)==ledger['nonzero_generator_entries']==1831,'nonzero entries')
check(sum(abs(v).bit_length() for v in entries)==ledger['sum_generator_entry_magnitude_bits']==21372,'magnitude bits')

# Independently replay the complete saved accepting witness, including extraction
# of a serial rewriting derivation from each separator-delimited tile block.
witness=json.loads((ROOT/'evidence/accepting-witness.json').read_text())
seq=witness['inner_tile_sequence']
w=witness['input']['configuration_word']
h=''.join(tiles[i]['h'] for i in seq)
g=''.join(tiles[i]['g'] for i in seq)
check(w+'#'+h==g+'X#','literal correspondence equation')
blocks_of_tiles=[[]]
for i in seq:
    if tiles[i]['h']=='#':
        check(tiles[i]['g']=='#','separator tile')
        blocks_of_tiles.append([])
    else:
        check('#' not in tiles[i]['h']+tiles[i]['g'],'private separator')
        blocks_of_tiles[-1].append(i)
check(blocks_of_tiles[-1]==[],'empty final tile segment')
serial_steps=0
for ids in blocks_of_tiles[:-1]:
    check(''.join(tiles[i]['g'] for i in ids)==w,'block source word')
    offset=0
    applications=[]
    for i in ids:
        tile=tiles[i]
        if tile['kind']=='rewrite':
            rule=rules[tile['rule_id']]
            check((rule['lhs'],rule['rhs'])==(tile['g'],tile['h']),'tile orientation')
            applications.append((offset,rule))
        else:
            check(tile['kind']=='copy' and tile['h']==tile['g'],'copy tile')
        offset+=len(tile['g'])
    # Disjoint rewrites commute after positional adjustment. Right-to-left replay
    # avoids any adjustment and checks serializability directly.
    for offset,rule in reversed(applications):
        check(w[offset:offset+len(rule['lhs'])]==rule['lhs'],'serial replay applicability')
        w=w[:offset]+rule['rhs']+w[offset+len(rule['lhs']):]
        serial_steps+=1
    check(w==''.join(tiles[i]['h'] for i in ids),'block target word')
check(w=='X','terminal')
prod=(I,I)
for name in witness['generator_word']:
    prod=tuple(mul(a,b) for a,b in zip(prod,G[name]))
target=blocks(witness['input']['target'])
check(prod==target==(inverse(phi(witness['input']['configuration_word']+'#')),T),'full witness target')

# Independently compare numerical bottom equality against abstract free-group
# equality and against the claimed exact generator language. Widely separated
# tile IDs exercise the full indexed numerical range, not just x_1 and x_2.
indices=(1,57,114)
names=tuple('A'+str(i) for i in indices)+tuple('B'+str(i) for i in indices)+('C',)
letters={}
for i in indices:
    letters['A'+str(i)]=(i+1,)
    letters['B'+str(i)]=(-1,-i-1,1)
letters['C']=(1,)

def append_reduced(reduced,suffix):
    out=list(reduced)
    for x in suffix:
        if out and out[-1]==-x:
            out.pop()
        else:
            out.append(x)
    return tuple(out)

def pattern(word):
    if word.count('C')!=1:
        return False
    k=word.index('C')
    return all(x[0]=='A' for x in word[:k]) and word[k+1:]==tuple('B'+x[1:] for x in reversed(word[:k]))

count=accepting=0
max_length=7

def visit(word,matrix,reduced):
    global count,accepting
    count+=1
    numerical=(matrix==T)
    formal=(reduced==(1,))
    expected=pattern(word)
    check(numerical==formal==expected,'marker counterexample: '+str(word))
    accepting+=numerical
    if len(word)<max_length:
        for name in names:
            visit(word+(name,),mul(matrix,G[name][1]),append_reduced(reduced,letters[name]))
visit((),I,())

result={
 'status':'pass',
 'method':'independent JSON-only implementation; no compiler or upstream imports',
 'numerical_generators_checked':len(G),
 'nonerasing_tiles_checked':len(tiles),
 'directed_rules_checked':len(rules),
 'accepting_witness_serial_steps':serial_steps,
 'accepting_witness_generator_length':len(witness['generator_word']),
 'marker_indices':list(indices),
 'marker_max_length':max_length,
 'marker_words_checked':count,
 'marker_words_equal_target':accepting,
 'semigroup_sha256':hashlib.sha256((ROOT/'data/semigroup.json').read_bytes()).hexdigest(),
 'caveat':'Finite checks supplement the general proof; they do not prove universal absence of spurious products or U15 universality.'
}
(ROOT/'audit/independent-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
