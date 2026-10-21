"""Conservative three-cell language of a symbolic tape half.

Affine lengths are overapproximated by every integer at least their
constant coefficient. Opaque lists are overapproximated by every finite
binary word. Thus absence of001 is a sound sufficient premise; false
rejections are possible, false acceptances are not.
"""
from itertools import product

def prefixes(atoms, width=3):
    words={''}
    for atom in atoms:
        enlarged=set()
        for word in words:
            n=width-len(word)
            if not n:enlarged.add(word);continue
            if atom[0]=='blank':extensions={'0'*n}
            elif atom[0]=='run':
                symbol,affine=atom[1:];constant=affine[0]
                assert constant>=0 and all(x>=0 for x in affine)
                lengths=range(min(constant,n),n+1)if any(affine[1:])else[min(constant,n)]
                extensions={str(symbol)*j for j in lengths}
            else:
                extensions={''.join(p)for j in range(n+1)for p in product('01',repeat=j)}
            enlarged.update(word+x for x in extensions)
        words=enlarged
        if all(len(w)==width for w in words):break
    assert all(len(w)==width for w in words),'Unrepresented exterior'
    return words

def install(symbolic, native34_legacy):
    old=symbolic.State.step
    receipt={'predicate':'Scanned cell and next two cells in the left scan direction do not equal001.',
             'symbolic_entry_count':0,'overapproximated_prefix_languages':set()}
    def checked_step(self,table,lemmas,clock,motion):
        if self.q==native34_legacy:
            self.key();assert self.direction==-1
            language=prefixes(self.left)
            assert '001'not in language,('Scanner relay premise unproved',language,self.key())
            receipt['symbolic_entry_count']+=1
            receipt['overapproximated_prefix_languages'].add(tuple(sorted(language)))
        return old(self,table,lemmas,clock,motion)
    symbolic.State.step=checked_step
    return receipt
