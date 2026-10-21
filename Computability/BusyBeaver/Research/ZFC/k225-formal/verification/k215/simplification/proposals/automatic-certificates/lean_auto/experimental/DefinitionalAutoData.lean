import BusyBeaver.ZFC.RMAutoCertificate
import BusyBeaver.ZFC.KSource215Data

namespace SetTheory.BusyBeaver.ZFC.KSource215Auto
open RegisterPath RMBisim RMNormalizedBisim KSource215 RMAutoCertificate
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

def inferredRows : List Entry := RMAutoCertificate.entries t215 tD
def block0 : CTree := balanced 32 ((inferredRows.drop 0).take 90)
def block1 : CTree := balanced 32 ((inferredRows.drop 90).take 90)
def block2 : CTree := balanced 32 ((inferredRows.drop 180).take 90)
def block3 : CTree := balanced 32 ((inferredRows.drop 270).take 90)
def block4 : CTree := balanced 32 ((inferredRows.drop 360).take 90)
def block5 : CTree := balanced 32 ((inferredRows.drop 450).take 90)
def block6 : CTree := balanced 32 ((inferredRows.drop 540).take 90)
def block7 : CTree := balanced 32 ((inferredRows.drop 630).take 90)
def block8 : CTree := balanced 32 ((inferredRows.drop 720).take 90)
def block9 : CTree := balanced 32 ((inferredRows.drop 810).take 90)
def block10 : CTree := balanced 32 ((inferredRows.drop 900).take 90)
def block11 : CTree := balanced 32 ((inferredRows.drop 990).take 90)
def block12 : CTree := balanced 32 ((inferredRows.drop 1080).take 90)
def block13 : CTree := balanced 32 ((inferredRows.drop 1170).take 90)
def block14 : CTree := balanced 32 ((inferredRows.drop 1260).take 90)
def block15 : CTree := balanced 32 ((inferredRows.drop 1350).take 76)

def inferredCertificate : CTree := .branch 720 (.branch 360 (.branch 180 (.branch 90 (block0) (block1)) (.branch 90 (block2) (block3))) (.branch 180 (.branch 90 (block4) (block5)) (.branch 90 (block6) (block7)))) (.branch 360 (.branch 180 (.branch 90 (block8) (block9)) (.branch 90 (block10) (block11))) (.branch 180 (.branch 90 (block12) (block13)) (.branch 90 (block14) (block15))))

def checkEntry : Entry → Bool := RMNormalizedBisim.entryOk t215 tD inferredCertificate

end SetTheory.BusyBeaver.ZFC.KSource215Auto
