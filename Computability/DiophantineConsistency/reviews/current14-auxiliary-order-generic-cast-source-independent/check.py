from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[2];orig=root/'Lean/DiophantineConsistency/CurrentAuxiliaryOrder2011.lean';draft=root/'research/current14-auxiliary-order-generic-cast-draft/CurrentAuxiliaryOrder2011.lean';provider=root/'Lean/DiophantineConsistency/PrimePowerOrder.lean'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(orig)=='67db5e89285d56908ce482ffd72108c909ccc5e4f505ac2d324157344048e08e' and sha(draft)=='1e173faa98191542bbd0c2853eb7065b2b30719137d6b1f315b0e09da9bf5974' and sha(provider)=='3e9cc789e4f685d8ab42690cde9545a002f516095de6783378a9600e1c25c421'
a=orig.read_text();b=draft.read_text();prefix='''theorem generator_order_succ (k : ℕ) :
    orderOf ((B : ZMod (auxiliary^(k+1)))^(auxiliary-1)) = auxiliary^k := by
  simpa only [Nat.cast_pow] using
    order_succ prime_auxiliary auxiliary_odd generator_dvd generator_not_square k

theorem generator_order (n : ℕ) (hn : 1 ≤ n) :
    orderOf ((B : ZMod (auxiliary^n))^(auxiliary-1)) = auxiliary^(n-1) := by
  simpa only [Nat.cast_pow] using
    order_prime_power prime_auxiliary auxiliary_odd generator_dvd generator_not_square hn
'''
replacement='''private theorem power_order_succ {p b e : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hd : p ∣ b^e-1) (hs : ¬ p^2 ∣ b^e-1) (k : ℕ) :
    orderOf ((b : ZMod (p^(k+1)))^e) = p^k := by
  simpa only [Nat.cast_pow] using order_succ hp ho hd hs k

private theorem power_order_prime {p b e n : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hd : p ∣ b^e-1) (hs : ¬ p^2 ∣ b^e-1) (hn : 1 ≤ n) :
    orderOf ((b : ZMod (p^n))^e) = p^(n-1) := by
  simpa only [Nat.cast_pow] using order_prime_power hp ho hd hs hn

theorem generator_order_succ (k : ℕ) :
    orderOf ((B : ZMod (auxiliary^(k+1)))^(auxiliary-1)) = auxiliary^k := by
  exact power_order_succ prime_auxiliary auxiliary_odd generator_dvd generator_not_square k

theorem generator_order (n : ℕ) (hn : 1 ≤ n) :
    orderOf ((B : ZMod (auxiliary^n))^(auxiliary-1)) = auxiliary^(n-1) := by
  exact power_order_prime prime_auxiliary auxiliary_odd generator_dvd generator_not_square hn
'''
assert a.count(prefix)==1 and a.replace(prefix,replacement)==b
p=provider.read_text();assert 'theorem order_succ {p g : ℕ} (hp : Nat.Prime p) (ho : Odd p)' in p and '(hd : p ∣ g-1) (hs : ¬ p^2 ∣ g-1) (k : ℕ)' in p and 'theorem order_prime_power {p g n : ℕ} (hp : Nat.Prime p) (ho : Odd p)' in p and '(hd : p ∣ g-1) (hs : ¬ p^2 ∣ g-1) (hn : 1 ≤ n)' in p
assert 'theorem generator_dvd : auxiliary ∣ B^(auxiliary-1)-1' in a and 'theorem generator_not_square : ¬ auxiliary^2 ∣ B^(auxiliary-1)-1' in a
print(json.dumps({'status':'PASS_SOURCE_ONLY','delta':'two private generic cast lemmas and two specialized proof bodies','specialization':'p=auxiliary, b=B, e=auxiliary-1','lean_run':False,'scope':'Mathematical signatures match; elaboration and memory untested'},indent=2))
