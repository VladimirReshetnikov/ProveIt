import BusyBeaver.ZFC.BisimRouting245Pilot

/-!
Public structural blocks of the already checked pilot's complete certificate.
No certificate entry is copied or changed. Each block is a projection of the
public full certificate; cert_decomposition proves exact reassembly.
This unit supplies data identities and the passed initial-segment proof only.
The 95 block checks and final halting equivalence are separate units.
-/
set_option autoImplicit false
namespace SetTheory.BusyBeaver.ZFC.BisimRouting245Data
open RegisterPath RMBisim

def cert : CTree := BisimRouting245Pilot.cert

theorem cert_eq : cert = BisimRouting245Pilot.cert := rfl

private def leftPart : CTree → CTree
  | .branch _ l _ => l
  | _ => .empty

private def rightPart : CTree → CTree
  | .branch _ _ r => r
  | _ => .empty

/-- Exact certificate indices [0, 32); structural path LLLLLL. -/
def chunk000 : CTree := leftPart (leftPart (leftPart (leftPart (leftPart (leftPart (cert))))))

/-- Exact certificate indices [32, 64); structural path LLLLLR. -/
def chunk001 : CTree := rightPart (leftPart (leftPart (leftPart (leftPart (leftPart (cert))))))

/-- Exact certificate indices [64, 96); structural path LLLLRL. -/
def chunk002 : CTree := leftPart (rightPart (leftPart (leftPart (leftPart (leftPart (cert))))))

/-- Exact certificate indices [96, 128); structural path LLLLRRL. -/
def chunk003 : CTree := leftPart (rightPart (rightPart (leftPart (leftPart (leftPart (leftPart (cert)))))))

/-- Exact certificate indices [128, 160); structural path LLLLRRR. -/
def chunk004 : CTree := rightPart (rightPart (rightPart (leftPart (leftPart (leftPart (leftPart (cert)))))))

/-- Exact certificate indices [160, 192); structural path LLLRLL. -/
def chunk005 : CTree := leftPart (leftPart (rightPart (leftPart (leftPart (leftPart (cert))))))

/-- Exact certificate indices [192, 224); structural path LLLRLRL. -/
def chunk006 : CTree := leftPart (rightPart (leftPart (rightPart (leftPart (leftPart (leftPart (cert)))))))

/-- Exact certificate indices [224, 256); structural path LLLRLRR. -/
def chunk007 : CTree := rightPart (rightPart (leftPart (rightPart (leftPart (leftPart (leftPart (cert)))))))

/-- Exact certificate indices [256, 288); structural path LLLRRL. -/
def chunk008 : CTree := leftPart (rightPart (rightPart (leftPart (leftPart (leftPart (cert))))))

/-- Exact certificate indices [288, 320); structural path LLLRRRL. -/
def chunk009 : CTree := leftPart (rightPart (rightPart (rightPart (leftPart (leftPart (leftPart (cert)))))))

/-- Exact certificate indices [320, 352); structural path LLLRRRR. -/
def chunk010 : CTree := rightPart (rightPart (rightPart (rightPart (leftPart (leftPart (leftPart (cert)))))))

/-- Exact certificate indices [352, 384); structural path LLRLLL. -/
def chunk011 : CTree := leftPart (leftPart (leftPart (rightPart (leftPart (leftPart (cert))))))

/-- Exact certificate indices [384, 416); structural path LLRLLRL. -/
def chunk012 : CTree := leftPart (rightPart (leftPart (leftPart (rightPart (leftPart (leftPart (cert)))))))

/-- Exact certificate indices [416, 448); structural path LLRLLRR. -/
def chunk013 : CTree := rightPart (rightPart (leftPart (leftPart (rightPart (leftPart (leftPart (cert)))))))

/-- Exact certificate indices [448, 480); structural path LLRLRL. -/
def chunk014 : CTree := leftPart (rightPart (leftPart (rightPart (leftPart (leftPart (cert))))))

/-- Exact certificate indices [480, 512); structural path LLRLRRL. -/
def chunk015 : CTree := leftPart (rightPart (rightPart (leftPart (rightPart (leftPart (leftPart (cert)))))))

/-- Exact certificate indices [512, 544); structural path LLRLRRR. -/
def chunk016 : CTree := rightPart (rightPart (rightPart (leftPart (rightPart (leftPart (leftPart (cert)))))))

/-- Exact certificate indices [544, 576); structural path LLRRLL. -/
def chunk017 : CTree := leftPart (leftPart (rightPart (rightPart (leftPart (leftPart (cert))))))

/-- Exact certificate indices [576, 608); structural path LLRRLRL. -/
def chunk018 : CTree := leftPart (rightPart (leftPart (rightPart (rightPart (leftPart (leftPart (cert)))))))

/-- Exact certificate indices [608, 640); structural path LLRRLRR. -/
def chunk019 : CTree := rightPart (rightPart (leftPart (rightPart (rightPart (leftPart (leftPart (cert)))))))

/-- Exact certificate indices [640, 672); structural path LLRRRL. -/
def chunk020 : CTree := leftPart (rightPart (rightPart (rightPart (leftPart (leftPart (cert))))))

/-- Exact certificate indices [672, 704); structural path LLRRRRL. -/
def chunk021 : CTree := leftPart (rightPart (rightPart (rightPart (rightPart (leftPart (leftPart (cert)))))))

/-- Exact certificate indices [704, 736); structural path LLRRRRR. -/
def chunk022 : CTree := rightPart (rightPart (rightPart (rightPart (rightPart (leftPart (leftPart (cert)))))))

/-- Exact certificate indices [736, 768); structural path LRLLLL. -/
def chunk023 : CTree := leftPart (leftPart (leftPart (leftPart (rightPart (leftPart (cert))))))

/-- Exact certificate indices [768, 800); structural path LRLLLRL. -/
def chunk024 : CTree := leftPart (rightPart (leftPart (leftPart (leftPart (rightPart (leftPart (cert)))))))

/-- Exact certificate indices [800, 832); structural path LRLLLRR. -/
def chunk025 : CTree := rightPart (rightPart (leftPart (leftPart (leftPart (rightPart (leftPart (cert)))))))

/-- Exact certificate indices [832, 864); structural path LRLLRL. -/
def chunk026 : CTree := leftPart (rightPart (leftPart (leftPart (rightPart (leftPart (cert))))))

/-- Exact certificate indices [864, 896); structural path LRLLRRL. -/
def chunk027 : CTree := leftPart (rightPart (rightPart (leftPart (leftPart (rightPart (leftPart (cert)))))))

/-- Exact certificate indices [896, 928); structural path LRLLRRR. -/
def chunk028 : CTree := rightPart (rightPart (rightPart (leftPart (leftPart (rightPart (leftPart (cert)))))))

/-- Exact certificate indices [928, 960); structural path LRLRLL. -/
def chunk029 : CTree := leftPart (leftPart (rightPart (leftPart (rightPart (leftPart (cert))))))

/-- Exact certificate indices [960, 992); structural path LRLRLRL. -/
def chunk030 : CTree := leftPart (rightPart (leftPart (rightPart (leftPart (rightPart (leftPart (cert)))))))

/-- Exact certificate indices [992, 1024); structural path LRLRLRR. -/
def chunk031 : CTree := rightPart (rightPart (leftPart (rightPart (leftPart (rightPart (leftPart (cert)))))))

/-- Exact certificate indices [1024, 1056); structural path LRLRRL. -/
def chunk032 : CTree := leftPart (rightPart (rightPart (leftPart (rightPart (leftPart (cert))))))

/-- Exact certificate indices [1056, 1088); structural path LRLRRRL. -/
def chunk033 : CTree := leftPart (rightPart (rightPart (rightPart (leftPart (rightPart (leftPart (cert)))))))

/-- Exact certificate indices [1088, 1120); structural path LRLRRRR. -/
def chunk034 : CTree := rightPart (rightPart (rightPart (rightPart (leftPart (rightPart (leftPart (cert)))))))

/-- Exact certificate indices [1120, 1152); structural path LRRLLL. -/
def chunk035 : CTree := leftPart (leftPart (leftPart (rightPart (rightPart (leftPart (cert))))))

/-- Exact certificate indices [1152, 1184); structural path LRRLLRL. -/
def chunk036 : CTree := leftPart (rightPart (leftPart (leftPart (rightPart (rightPart (leftPart (cert)))))))

/-- Exact certificate indices [1184, 1216); structural path LRRLLRR. -/
def chunk037 : CTree := rightPart (rightPart (leftPart (leftPart (rightPart (rightPart (leftPart (cert)))))))

/-- Exact certificate indices [1216, 1248); structural path LRRLRL. -/
def chunk038 : CTree := leftPart (rightPart (leftPart (rightPart (rightPart (leftPart (cert))))))

/-- Exact certificate indices [1248, 1280); structural path LRRLRRL. -/
def chunk039 : CTree := leftPart (rightPart (rightPart (leftPart (rightPart (rightPart (leftPart (cert)))))))

/-- Exact certificate indices [1280, 1312); structural path LRRLRRR. -/
def chunk040 : CTree := rightPart (rightPart (rightPart (leftPart (rightPart (rightPart (leftPart (cert)))))))

/-- Exact certificate indices [1312, 1344); structural path LRRRLL. -/
def chunk041 : CTree := leftPart (leftPart (rightPart (rightPart (rightPart (leftPart (cert))))))

/-- Exact certificate indices [1344, 1376); structural path LRRRLRL. -/
def chunk042 : CTree := leftPart (rightPart (leftPart (rightPart (rightPart (rightPart (leftPart (cert)))))))

/-- Exact certificate indices [1376, 1408); structural path LRRRLRR. -/
def chunk043 : CTree := rightPart (rightPart (leftPart (rightPart (rightPart (rightPart (leftPart (cert)))))))

/-- Exact certificate indices [1408, 1440); structural path LRRRRL. -/
def chunk044 : CTree := leftPart (rightPart (rightPart (rightPart (rightPart (leftPart (cert))))))

/-- Exact certificate indices [1440, 1472); structural path LRRRRRL. -/
def chunk045 : CTree := leftPart (rightPart (rightPart (rightPart (rightPart (rightPart (leftPart (cert)))))))

/-- Exact certificate indices [1472, 1504); structural path LRRRRRR. -/
def chunk046 : CTree := rightPart (rightPart (rightPart (rightPart (rightPart (rightPart (leftPart (cert)))))))

/-- Exact certificate indices [1504, 1536); structural path RLLLLL. -/
def chunk047 : CTree := leftPart (leftPart (leftPart (leftPart (leftPart (rightPart (cert))))))

/-- Exact certificate indices [1536, 1568); structural path RLLLLRL. -/
def chunk048 : CTree := leftPart (rightPart (leftPart (leftPart (leftPart (leftPart (rightPart (cert)))))))

/-- Exact certificate indices [1568, 1600); structural path RLLLLRR. -/
def chunk049 : CTree := rightPart (rightPart (leftPart (leftPart (leftPart (leftPart (rightPart (cert)))))))

/-- Exact certificate indices [1600, 1632); structural path RLLLRL. -/
def chunk050 : CTree := leftPart (rightPart (leftPart (leftPart (leftPart (rightPart (cert))))))

/-- Exact certificate indices [1632, 1664); structural path RLLLRRL. -/
def chunk051 : CTree := leftPart (rightPart (rightPart (leftPart (leftPart (leftPart (rightPart (cert)))))))

/-- Exact certificate indices [1664, 1696); structural path RLLLRRR. -/
def chunk052 : CTree := rightPart (rightPart (rightPart (leftPart (leftPart (leftPart (rightPart (cert)))))))

/-- Exact certificate indices [1696, 1728); structural path RLLRLL. -/
def chunk053 : CTree := leftPart (leftPart (rightPart (leftPart (leftPart (rightPart (cert))))))

/-- Exact certificate indices [1728, 1760); structural path RLLRLRL. -/
def chunk054 : CTree := leftPart (rightPart (leftPart (rightPart (leftPart (leftPart (rightPart (cert)))))))

/-- Exact certificate indices [1760, 1792); structural path RLLRLRR. -/
def chunk055 : CTree := rightPart (rightPart (leftPart (rightPart (leftPart (leftPart (rightPart (cert)))))))

/-- Exact certificate indices [1792, 1824); structural path RLLRRL. -/
def chunk056 : CTree := leftPart (rightPart (rightPart (leftPart (leftPart (rightPart (cert))))))

/-- Exact certificate indices [1824, 1856); structural path RLLRRRL. -/
def chunk057 : CTree := leftPart (rightPart (rightPart (rightPart (leftPart (leftPart (rightPart (cert)))))))

/-- Exact certificate indices [1856, 1888); structural path RLLRRRR. -/
def chunk058 : CTree := rightPart (rightPart (rightPart (rightPart (leftPart (leftPart (rightPart (cert)))))))

/-- Exact certificate indices [1888, 1920); structural path RLRLLL. -/
def chunk059 : CTree := leftPart (leftPart (leftPart (rightPart (leftPart (rightPart (cert))))))

/-- Exact certificate indices [1920, 1952); structural path RLRLLRL. -/
def chunk060 : CTree := leftPart (rightPart (leftPart (leftPart (rightPart (leftPart (rightPart (cert)))))))

/-- Exact certificate indices [1952, 1984); structural path RLRLLRR. -/
def chunk061 : CTree := rightPart (rightPart (leftPart (leftPart (rightPart (leftPart (rightPart (cert)))))))

/-- Exact certificate indices [1984, 2016); structural path RLRLRL. -/
def chunk062 : CTree := leftPart (rightPart (leftPart (rightPart (leftPart (rightPart (cert))))))

/-- Exact certificate indices [2016, 2048); structural path RLRLRRL. -/
def chunk063 : CTree := leftPart (rightPart (rightPart (leftPart (rightPart (leftPart (rightPart (cert)))))))

/-- Exact certificate indices [2048, 2080); structural path RLRLRRR. -/
def chunk064 : CTree := rightPart (rightPart (rightPart (leftPart (rightPart (leftPart (rightPart (cert)))))))

/-- Exact certificate indices [2080, 2112); structural path RLRRLL. -/
def chunk065 : CTree := leftPart (leftPart (rightPart (rightPart (leftPart (rightPart (cert))))))

/-- Exact certificate indices [2112, 2144); structural path RLRRLRL. -/
def chunk066 : CTree := leftPart (rightPart (leftPart (rightPart (rightPart (leftPart (rightPart (cert)))))))

/-- Exact certificate indices [2144, 2176); structural path RLRRLRR. -/
def chunk067 : CTree := rightPart (rightPart (leftPart (rightPart (rightPart (leftPart (rightPart (cert)))))))

/-- Exact certificate indices [2176, 2208); structural path RLRRRL. -/
def chunk068 : CTree := leftPart (rightPart (rightPart (rightPart (leftPart (rightPart (cert))))))

/-- Exact certificate indices [2208, 2240); structural path RLRRRRL. -/
def chunk069 : CTree := leftPart (rightPart (rightPart (rightPart (rightPart (leftPart (rightPart (cert)))))))

/-- Exact certificate indices [2240, 2272); structural path RLRRRRR. -/
def chunk070 : CTree := rightPart (rightPart (rightPart (rightPart (rightPart (leftPart (rightPart (cert)))))))

/-- Exact certificate indices [2272, 2304); structural path RRLLLL. -/
def chunk071 : CTree := leftPart (leftPart (leftPart (leftPart (rightPart (rightPart (cert))))))

/-- Exact certificate indices [2304, 2336); structural path RRLLLRL. -/
def chunk072 : CTree := leftPart (rightPart (leftPart (leftPart (leftPart (rightPart (rightPart (cert)))))))

/-- Exact certificate indices [2336, 2368); structural path RRLLLRR. -/
def chunk073 : CTree := rightPart (rightPart (leftPart (leftPart (leftPart (rightPart (rightPart (cert)))))))

/-- Exact certificate indices [2368, 2400); structural path RRLLRL. -/
def chunk074 : CTree := leftPart (rightPart (leftPart (leftPart (rightPart (rightPart (cert))))))

/-- Exact certificate indices [2400, 2432); structural path RRLLRRL. -/
def chunk075 : CTree := leftPart (rightPart (rightPart (leftPart (leftPart (rightPart (rightPart (cert)))))))

/-- Exact certificate indices [2432, 2464); structural path RRLLRRR. -/
def chunk076 : CTree := rightPart (rightPart (rightPart (leftPart (leftPart (rightPart (rightPart (cert)))))))

/-- Exact certificate indices [2464, 2496); structural path RRLRLL. -/
def chunk077 : CTree := leftPart (leftPart (rightPart (leftPart (rightPart (rightPart (cert))))))

/-- Exact certificate indices [2496, 2528); structural path RRLRLRL. -/
def chunk078 : CTree := leftPart (rightPart (leftPart (rightPart (leftPart (rightPart (rightPart (cert)))))))

/-- Exact certificate indices [2528, 2560); structural path RRLRLRR. -/
def chunk079 : CTree := rightPart (rightPart (leftPart (rightPart (leftPart (rightPart (rightPart (cert)))))))

/-- Exact certificate indices [2560, 2592); structural path RRLRRL. -/
def chunk080 : CTree := leftPart (rightPart (rightPart (leftPart (rightPart (rightPart (cert))))))

/-- Exact certificate indices [2592, 2624); structural path RRLRRRL. -/
def chunk081 : CTree := leftPart (rightPart (rightPart (rightPart (leftPart (rightPart (rightPart (cert)))))))

/-- Exact certificate indices [2624, 2656); structural path RRLRRRR. -/
def chunk082 : CTree := rightPart (rightPart (rightPart (rightPart (leftPart (rightPart (rightPart (cert)))))))

/-- Exact certificate indices [2656, 2688); structural path RRRLLL. -/
def chunk083 : CTree := leftPart (leftPart (leftPart (rightPart (rightPart (rightPart (cert))))))

/-- Exact certificate indices [2688, 2720); structural path RRRLLRL. -/
def chunk084 : CTree := leftPart (rightPart (leftPart (leftPart (rightPart (rightPart (rightPart (cert)))))))

/-- Exact certificate indices [2720, 2752); structural path RRRLLRR. -/
def chunk085 : CTree := rightPart (rightPart (leftPart (leftPart (rightPart (rightPart (rightPart (cert)))))))

/-- Exact certificate indices [2752, 2784); structural path RRRLRL. -/
def chunk086 : CTree := leftPart (rightPart (leftPart (rightPart (rightPart (rightPart (cert))))))

/-- Exact certificate indices [2784, 2816); structural path RRRLRRL. -/
def chunk087 : CTree := leftPart (rightPart (rightPart (leftPart (rightPart (rightPart (rightPart (cert)))))))

/-- Exact certificate indices [2816, 2848); structural path RRRLRRR. -/
def chunk088 : CTree := rightPart (rightPart (rightPart (leftPart (rightPart (rightPart (rightPart (cert)))))))

/-- Exact certificate indices [2848, 2880); structural path RRRRLL. -/
def chunk089 : CTree := leftPart (leftPart (rightPart (rightPart (rightPart (rightPart (cert))))))

/-- Exact certificate indices [2880, 2912); structural path RRRRLRL. -/
def chunk090 : CTree := leftPart (rightPart (leftPart (rightPart (rightPart (rightPart (rightPart (cert)))))))

/-- Exact certificate indices [2912, 2944); structural path RRRRLRR. -/
def chunk091 : CTree := rightPart (rightPart (leftPart (rightPart (rightPart (rightPart (rightPart (cert)))))))

/-- Exact certificate indices [2944, 2976); structural path RRRRRL. -/
def chunk092 : CTree := leftPart (rightPart (rightPart (rightPart (rightPart (rightPart (cert))))))

/-- Exact certificate indices [2976, 3008); structural path RRRRRRL. -/
def chunk093 : CTree := leftPart (rightPart (rightPart (rightPart (rightPart (rightPart (rightPart (cert)))))))

/-- Exact certificate indices [3008, 3013); structural path RRRRRRR. -/
def chunk094 : CTree := rightPart (rightPart (rightPart (rightPart (rightPart (rightPart (rightPart (cert)))))))

/-- Balanced reassembly with the original left-subtree sizes. -/
def assembly : CTree :=
  .branch 1504 (.branch 736 (.branch 352 (.branch 160 (.branch 64 (.branch 32 (chunk000) (chunk001)) (.branch 32 (chunk002) (.branch 32 (chunk003) (chunk004)))) (.branch 96 (.branch 32 (chunk005) (.branch 32 (chunk006) (chunk007))) (.branch 32 (chunk008) (.branch 32 (chunk009) (chunk010))))) (.branch 192 (.branch 96 (.branch 32 (chunk011) (.branch 32 (chunk012) (chunk013))) (.branch 32 (chunk014) (.branch 32 (chunk015) (chunk016)))) (.branch 96 (.branch 32 (chunk017) (.branch 32 (chunk018) (chunk019))) (.branch 32 (chunk020) (.branch 32 (chunk021) (chunk022)))))) (.branch 384 (.branch 192 (.branch 96 (.branch 32 (chunk023) (.branch 32 (chunk024) (chunk025))) (.branch 32 (chunk026) (.branch 32 (chunk027) (chunk028)))) (.branch 96 (.branch 32 (chunk029) (.branch 32 (chunk030) (chunk031))) (.branch 32 (chunk032) (.branch 32 (chunk033) (chunk034))))) (.branch 192 (.branch 96 (.branch 32 (chunk035) (.branch 32 (chunk036) (chunk037))) (.branch 32 (chunk038) (.branch 32 (chunk039) (chunk040)))) (.branch 96 (.branch 32 (chunk041) (.branch 32 (chunk042) (chunk043))) (.branch 32 (chunk044) (.branch 32 (chunk045) (chunk046))))))) (.branch 768 (.branch 384 (.branch 192 (.branch 96 (.branch 32 (chunk047) (.branch 32 (chunk048) (chunk049))) (.branch 32 (chunk050) (.branch 32 (chunk051) (chunk052)))) (.branch 96 (.branch 32 (chunk053) (.branch 32 (chunk054) (chunk055))) (.branch 32 (chunk056) (.branch 32 (chunk057) (chunk058))))) (.branch 192 (.branch 96 (.branch 32 (chunk059) (.branch 32 (chunk060) (chunk061))) (.branch 32 (chunk062) (.branch 32 (chunk063) (chunk064)))) (.branch 96 (.branch 32 (chunk065) (.branch 32 (chunk066) (chunk067))) (.branch 32 (chunk068) (.branch 32 (chunk069) (chunk070)))))) (.branch 384 (.branch 192 (.branch 96 (.branch 32 (chunk071) (.branch 32 (chunk072) (chunk073))) (.branch 32 (chunk074) (.branch 32 (chunk075) (chunk076)))) (.branch 96 (.branch 32 (chunk077) (.branch 32 (chunk078) (chunk079))) (.branch 32 (chunk080) (.branch 32 (chunk081) (chunk082))))) (.branch 192 (.branch 96 (.branch 32 (chunk083) (.branch 32 (chunk084) (chunk085))) (.branch 32 (chunk086) (.branch 32 (chunk087) (chunk088)))) (.branch 96 (.branch 32 (chunk089) (.branch 32 (chunk090) (chunk091))) (.branch 32 (chunk092) (.branch 32 (chunk093) (chunk094)))))))

/-- This identity prevents omissions, duplicated blocks, or empty projections. -/
theorem cert_decomposition : cert = assembly := rfl

/-- The checker relation always uses the full certificate for successor lookup. -/
def test : Entry → Bool := entryOk ActualTree254.tree TreeRouting245.tree cert

/-- Generic structural decomposition; no semantic entry checks are assumed. -/
theorem allC_decomposition (f : Entry → Bool) :
    allC f cert =
      (((((((allC f chunk000) && (allC f chunk001)) && ((allC f chunk002) && ((allC f chunk003) && (allC f chunk004)))) && (((allC f chunk005) && ((allC f chunk006) && (allC f chunk007))) && ((allC f chunk008) && ((allC f chunk009) && (allC f chunk010))))) && ((((allC f chunk011) && ((allC f chunk012) && (allC f chunk013))) && ((allC f chunk014) && ((allC f chunk015) && (allC f chunk016)))) && (((allC f chunk017) && ((allC f chunk018) && (allC f chunk019))) && ((allC f chunk020) && ((allC f chunk021) && (allC f chunk022)))))) && (((((allC f chunk023) && ((allC f chunk024) && (allC f chunk025))) && ((allC f chunk026) && ((allC f chunk027) && (allC f chunk028)))) && (((allC f chunk029) && ((allC f chunk030) && (allC f chunk031))) && ((allC f chunk032) && ((allC f chunk033) && (allC f chunk034))))) && ((((allC f chunk035) && ((allC f chunk036) && (allC f chunk037))) && ((allC f chunk038) && ((allC f chunk039) && (allC f chunk040)))) && (((allC f chunk041) && ((allC f chunk042) && (allC f chunk043))) && ((allC f chunk044) && ((allC f chunk045) && (allC f chunk046))))))) && ((((((allC f chunk047) && ((allC f chunk048) && (allC f chunk049))) && ((allC f chunk050) && ((allC f chunk051) && (allC f chunk052)))) && (((allC f chunk053) && ((allC f chunk054) && (allC f chunk055))) && ((allC f chunk056) && ((allC f chunk057) && (allC f chunk058))))) && ((((allC f chunk059) && ((allC f chunk060) && (allC f chunk061))) && ((allC f chunk062) && ((allC f chunk063) && (allC f chunk064)))) && (((allC f chunk065) && ((allC f chunk066) && (allC f chunk067))) && ((allC f chunk068) && ((allC f chunk069) && (allC f chunk070)))))) && (((((allC f chunk071) && ((allC f chunk072) && (allC f chunk073))) && ((allC f chunk074) && ((allC f chunk075) && (allC f chunk076)))) && (((allC f chunk077) && ((allC f chunk078) && (allC f chunk079))) && ((allC f chunk080) && ((allC f chunk081) && (allC f chunk082))))) && ((((allC f chunk083) && ((allC f chunk084) && (allC f chunk085))) && ((allC f chunk086) && ((allC f chunk087) && (allC f chunk088)))) && (((allC f chunk089) && ((allC f chunk090) && (allC f chunk091))) && ((allC f chunk092) && ((allC f chunk093) && (allC f chunk094)))))))) := by
  rw [cert_decomposition]
  rfl

/-- Reuse only the exact passed initial-segment theorem. -/
theorem initial_ok :
    branchOk ActualTree254.tree TreeRouting245.tree cert [] [] 0 = true :=
  BisimRouting245Pilot.initial_ok

end SetTheory.BusyBeaver.ZFC.BisimRouting245Data
