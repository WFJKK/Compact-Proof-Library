import CompactCheck.Json
import CompactCheck.Spec
import CompactCheck.Counted

/-!
# Protected target: network `max2_tiny-v8-s0`, claimed count 64

Written by scripts/make_protected.py from a network file of scripts/export_network.py. Not to be edited:
the acceptance service generates it, and checks its constants against the file with the checker's reader.
-/

namespace Protected.N_max2_tiny_v8_s0_c64

open CompactCheck

/-- The network's graph, operation by operation, as the file gives it. -/
def graph : Graph := {
  positions := 2
  values := 8
  nodes := [
    Op.input,
    Op.sum 0 1,
    Op.linear 1 "embedding.weight" none,
    Op.linear 2 "linear.weight" none,
    Op.linear 3 "unembedding.weight" none]
  output := 4 }

/-- The network's weights, every entry an exact dyadic rational. -/
def weights : Weights ℚ := [
    ("embedding.weight", ({ shape := [4, 8], data := #[dyadic 1505767040 (-32 : Int), dyadic 3579024640 (-32 : Int), dyadic (-2723229184 : Int) (-32 : Int), dyadic (-4552834048 : Int) (-32 : Int), dyadic (-1244547584 : Int) (-32 : Int), dyadic (-5969323520 : Int) (-32 : Int), dyadic (-1187631616 : Int) (-32 : Int), dyadic 8063848448 (-32 : Int), dyadic 1850068736 (-32 : Int), dyadic 5897028608 (-32 : Int), dyadic 2699719936 (-32 : Int), dyadic 1405767680 (-32 : Int), dyadic (-7354245120 : Int) (-32 : Int), dyadic 3162449408 (-32 : Int), dyadic (-6038616064 : Int) (-32 : Int), dyadic (-3815782912 : Int) (-32 : Int), dyadic 3315320576 (-32 : Int), dyadic (-2201740544 : Int) (-32 : Int), dyadic (-6558562304 : Int) (-32 : Int), dyadic (-6718392832 : Int) (-32 : Int), dyadic (-6734084608 : Int) (-32 : Int), dyadic 7755095040 (-32 : Int), dyadic 7506880512 (-32 : Int), dyadic (-4102060544 : Int) (-32 : Int), dyadic 8556537 (-32 : Int), dyadic (-3347454976 : Int) (-32 : Int), dyadic 3662328320 (-32 : Int), dyadic (-4168690688 : Int) (-32 : Int), dyadic (-1362898688 : Int) (-32 : Int), dyadic 6568083968 (-32 : Int), dyadic (-5969057792 : Int) (-32 : Int), dyadic 7601166848 (-32 : Int)] } : Tensor ℚ)),
    ("linear.weight", ({ shape := [4, 4], data := #[dyadic (-65440052 : Int) (-25 : Int), dyadic (-14775917 : Int) (-25 : Int), dyadic (-61942512 : Int) (-25 : Int), dyadic (-87986648 : Int) (-25 : Int), dyadic (-59045908 : Int) (-25 : Int), dyadic 63969980 (-25 : Int), dyadic 57680444 (-25 : Int), dyadic (-35835776 : Int) (-25 : Int), dyadic 41814268 (-25 : Int), dyadic (-48663036 : Int) (-25 : Int), dyadic 41754616 (-25 : Int), dyadic (-74230168 : Int) (-25 : Int), dyadic (-70770936 : Int) (-25 : Int), dyadic (-51214836 : Int) (-25 : Int), dyadic 64270508 (-25 : Int), dyadic (-12373595 : Int) (-25 : Int)] } : Tensor ℚ)),
    ("unembedding.weight", ({ shape := [8, 4], data := #[dyadic (-450605664 : Int) (-28 : Int), dyadic 323598432 (-28 : Int), dyadic 355664416 (-28 : Int), dyadic 89023992 (-28 : Int), dyadic (-49482180 : Int) (-28 : Int), dyadic 341758112 (-28 : Int), dyadic 282592480 (-28 : Int), dyadic (-587080320 : Int) (-28 : Int), dyadic (-114234072 : Int) (-28 : Int), dyadic 56890200 (-28 : Int), dyadic (-485857824 : Int) (-28 : Int), dyadic (-389536512 : Int) (-28 : Int), dyadic 500002080 (-28 : Int), dyadic 364990112 (-28 : Int), dyadic (-195271120 : Int) (-28 : Int), dyadic (-108815296 : Int) (-28 : Int), dyadic 439405888 (-28 : Int), dyadic (-442649888 : Int) (-28 : Int), dyadic 132182792 (-28 : Int), dyadic 13021035 (-28 : Int), dyadic (-94760784 : Int) (-28 : Int), dyadic 479725216 (-28 : Int), dyadic (-448471072 : Int) (-28 : Int), dyadic 392036160 (-28 : Int), dyadic 224557968 (-28 : Int), dyadic 400899008 (-28 : Int), dyadic 525075808 (-28 : Int), dyadic 507013952 (-28 : Int), dyadic (-399440736 : Int) (-28 : Int), dyadic (-537098624 : Int) (-28 : Int), dyadic (-9586184 : Int) (-28 : Int), dyadic (-358741920 : Int) (-28 : Int)] } : Tensor ℚ))]

/-- The task, as `taskByName` builds it for this input shape. -/
def task : Task := maxTask 2 8

/-- The certificate of a scored submission, as the manifest gives it (0 numbers); a checker reads
    it through `CostM.cert`. -/
def cert : Cert := #[]

/-- The number of inputs the candidate claims the network answers correctly. -/
def claimedCount : Nat := 64

/-- What a candidate has to prove: the network answers at least `claimedCount` of its
    64 inputs correctly, in the sense of `Spec.lean`. -/
def Target : Prop := claimedCount ≤ numCorrect graph weights task

end Protected.N_max2_tiny_v8_s0_c64
