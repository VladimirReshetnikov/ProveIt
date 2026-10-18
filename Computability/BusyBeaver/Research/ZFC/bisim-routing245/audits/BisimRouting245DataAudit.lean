import BusyBeaver.ZFC.BisimRouting245Data
open SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim BisimRouting245Data
#print axioms BisimRouting245Data.cert_eq
#print axioms BisimRouting245Data.cert_decomposition
#print axioms BisimRouting245Data.allC_decomposition
#print axioms BisimRouting245Data.initial_ok

example : cert = BisimRouting245Pilot.cert := cert_eq
example : cert = assembly := cert_decomposition
example (f : Entry → Bool) : allC f cert =
    (((((((allC f chunk000) && (allC f chunk001)) && ((allC f chunk002) && ((allC f chunk003) && (allC f chunk004)))) && (((allC f chunk005) && ((allC f chunk006) && (allC f chunk007))) && ((allC f chunk008) && ((allC f chunk009) && (allC f chunk010))))) && ((((allC f chunk011) && ((allC f chunk012) && (allC f chunk013))) && ((allC f chunk014) && ((allC f chunk015) && (allC f chunk016)))) && (((allC f chunk017) && ((allC f chunk018) && (allC f chunk019))) && ((allC f chunk020) && ((allC f chunk021) && (allC f chunk022)))))) && (((((allC f chunk023) && ((allC f chunk024) && (allC f chunk025))) && ((allC f chunk026) && ((allC f chunk027) && (allC f chunk028)))) && (((allC f chunk029) && ((allC f chunk030) && (allC f chunk031))) && ((allC f chunk032) && ((allC f chunk033) && (allC f chunk034))))) && ((((allC f chunk035) && ((allC f chunk036) && (allC f chunk037))) && ((allC f chunk038) && ((allC f chunk039) && (allC f chunk040)))) && (((allC f chunk041) && ((allC f chunk042) && (allC f chunk043))) && ((allC f chunk044) && ((allC f chunk045) && (allC f chunk046))))))) && ((((((allC f chunk047) && ((allC f chunk048) && (allC f chunk049))) && ((allC f chunk050) && ((allC f chunk051) && (allC f chunk052)))) && (((allC f chunk053) && ((allC f chunk054) && (allC f chunk055))) && ((allC f chunk056) && ((allC f chunk057) && (allC f chunk058))))) && ((((allC f chunk059) && ((allC f chunk060) && (allC f chunk061))) && ((allC f chunk062) && ((allC f chunk063) && (allC f chunk064)))) && (((allC f chunk065) && ((allC f chunk066) && (allC f chunk067))) && ((allC f chunk068) && ((allC f chunk069) && (allC f chunk070)))))) && (((((allC f chunk071) && ((allC f chunk072) && (allC f chunk073))) && ((allC f chunk074) && ((allC f chunk075) && (allC f chunk076)))) && (((allC f chunk077) && ((allC f chunk078) && (allC f chunk079))) && ((allC f chunk080) && ((allC f chunk081) && (allC f chunk082))))) && ((((allC f chunk083) && ((allC f chunk084) && (allC f chunk085))) && ((allC f chunk086) && ((allC f chunk087) && (allC f chunk088)))) && (((allC f chunk089) && ((allC f chunk090) && (allC f chunk091))) && ((allC f chunk092) && ((allC f chunk093) && (allC f chunk094)))))))) := allC_decomposition f
example : branchOk ActualTree254.tree TreeRouting245.tree cert [] [] 0 = true := initial_ok
example (f : Entry → Bool) (h : allC f assembly = true) : allC f cert = true := by
  rw [cert_decomposition]
  exact h
