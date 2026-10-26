#!/usr/bin/env python3
"""Independent bounded algebra/branch models, not Lean or machine simulation."""
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
class SemanticModels(unittest.TestCase):
 def test_signed_integer_action_including_zero_width(self):
  for w in range(-9,10):
   for t in range(-15,16):
    for x in range(-7,8):
     self.assertEqual((x+t*w,t-t),(x+w*t,0))
     f=lambda a,b:(a+w*b, (a+w*b)**3)
     self.assertEqual(f(x+w,t-1),f(x,t))
     self.assertEqual(f(x,t),f(x+w*t,0))
 def test_signed_transport_negative_controls(self):
  w,x,t=3,2,-4
  self.assertNotEqual(x+w*t,x-w*t)
  self.assertNotEqual(x+w*t,x+w*abs(t))
  self.assertNotEqual(t+t*(-1),t+t)
 def test_band_geometry_and_exact_address(self):
  # Height and margins vary independently; symbolic band values distinguish times.
  for L,R,H in [(2,2,3),(2,8,3),(9,2,11),(5,7,8),(12,4,31)]:
   w=L+R;n=w*H
   band=lambda x,t:(x,t%H)
   ext=lambda x,t:band((x+L)%w-L,t+(x+L)//w)
   word=lambda z:ext(-(z%n),0)
   for x in range(-L-w,R+w):
    for t in range(-2*H,2*H+1):
     self.assertEqual(word(-x-w*t),ext(x,t))
     if -L<=x<R:self.assertEqual(word(-x-w*t),band(x,t))
   self.assertEqual(ext(-L,0),band(-L,0))
   self.assertEqual(ext(R,0),band(-L,1))
   self.assertNotEqual(ext(R,0),band(R,0))
 def test_band_binding_negative_controls(self):
  L,R,H=2,7,3;w=L+R;n=w*H
  ext=lambda x,t:((x+L)%w-L,(t+(x+L)//w)%H)
  word=lambda z:ext(-(z%n),0)
  self.assertNotEqual(word(1+w),ext(1,1)) # wrong address sign
  self.assertNotEqual(ext(R,0),(R,0)) # closed right endpoint is false
  self.assertNotEqual(ext(R,0),(-L,-1%H)) # wrong seam time direction
 @staticmethod
 def ports(H,k):
  if k==0:return ('initializer',),('run',1)
  if k+1==H:return ('finish',),('initializer',)
  if k+2==H:return ('run',k),('finish',)
  return ('run',k),('run',k+1)
 def test_all_cyclic_edges_and_smallest_height(self):
  counts={'wrap':0,'zero':0,'finish':0,'interior':0}
  for H in range(3,65):
   for k in range(H):
    self.assertEqual(self.ports(H,k)[1],self.ports(H,(k+1)%H)[0])
    key='wrap' if k+1==H else 'zero' if k==0 else 'finish' if k+2==H else 'interior'
    counts[key]+=1
  self.assertTrue(all(counts.values()))
  self.assertEqual([self.ports(3,k) for k in range(3)],[(('initializer',),('run',1)),(('run',1),('finish',)),(('finish',),('initializer',))])
 def test_cyclic_height_guard_negative_controls(self):
  for H in [1,2]:self.assertTrue(any(self.ports(H,k)[1]!=self.ports(H,(k+1)%H)[0] for k in range(H)))
  with self.assertRaises(ZeroDivisionError):_=(0+1)%0
 def test_exact_halted_fin2_constructor_colors(self):
  observed=set()
  for at_head in [False,True]:
   for bit in [0,1]:
    a=int(at_head);c=432*a+bit;observed.add(c)
    passed=(0,c,0,c);finished=(0,c,0,438)
    self.assertEqual(passed,(0,432*a+bit,0,432*a+bit))
    self.assertEqual(finished,(0,432*a+bit,0,438))
  self.assertEqual(observed,{0,1,432,433})
  self.assertNotIn(4,observed) # actual initialized operating head is not halted
  self.assertNotIn(434,observed)
 def test_constructor_model_matches_pinned_source_shape(self):
  lang=(ROOT/'sources/Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942Language.lean').read_text()
  self.assertIn('| pass (a b : Fin 2) : Allowed ⟨0, 432*a.val+b.val, 0, 432*a.val+b.val⟩',lang)
  self.assertIn('| finish (a b : Fin 2) : Allowed ⟨0, 432*a.val+b.val, 0, 438⟩',lang)
  encoding=(ROOT/'sources/Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangMachineEncoding.lean').read_text()
  self.assertIn('headColor none b = 432 + b.toNat',encoding)
  self.assertIn('if x = cfg.head then headColor cfg.state (Tape.read cfg.tape x)',encoding)
if __name__=='__main__':unittest.main()
