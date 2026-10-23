import CompactCheck.Json
import CompactCheck.Spec
import CompactCheck.Counted

/-!
# Protected target: network `attn_min2_tiny-v8d4-s1`, claimed count 64

Written by scripts/make_protected.py from a network file of scripts/export_network.py. Not to be edited:
the acceptance service generates it, and checks its constants against the file with the checker's reader.
-/

namespace Protected.N_attn_min2_tiny_v8d4_s1_c64

open CompactCheck

/-- The network's graph, operation by operation, as the file gives it. -/
def graph : Graph := {
  positions := 2
  values := 8
  nodes := [
    Op.input,
    Op.param "E",
    Op.matmul 0 1,
    Op.param "P",
    Op.binary BinOp.add 2 3,
    Op.index 4 [IndexItem.all, IndexItem.one 1],
    Op.param "WQ",
    Op.matmul 5 6,
    Op.param "#const0",
    Op.binary BinOp.mul 7 8,
    Op.param "WK",
    Op.matmul 4 10,
    Op.param "WV",
    Op.matmul 4 12,
    Op.unsqueeze 9 1,
    Op.binary BinOp.mul 11 14,
    Op.sum 15 2,
    Op.softmax 16 1,
    Op.unsqueeze 17 2,
    Op.binary BinOp.mul 18 13,
    Op.sum 19 1,
    Op.param "WO",
    Op.matmul 20 21,
    Op.binary BinOp.add 5 22,
    Op.param "U",
    Op.matmul 23 24]
  output := 25 }

/-- The network's weights, every entry an exact dyadic rational. -/
def weights : Weights ℚ := [
    ("E", ({ shape := [8, 4], data := #[dyadic 467686592 (-29 : Int), dyadic 327706336 (-29 : Int), dyadic (-472663328 : Int) (-29 : Int), dyadic (-470445344 : Int) (-29 : Int), dyadic (-557223936 : Int) (-29 : Int), dyadic (-453742976 : Int) (-29 : Int), dyadic 393394720 (-29 : Int), dyadic (-361150496 : Int) (-29 : Int), dyadic 550486720 (-29 : Int), dyadic (-334274080 : Int) (-29 : Int), dyadic 449615328 (-29 : Int), dyadic (-79746896 : Int) (-29 : Int), dyadic (-314705568 : Int) (-29 : Int), dyadic (-370093536 : Int) (-29 : Int), dyadic (-476270720 : Int) (-29 : Int), dyadic (-157847376 : Int) (-29 : Int), dyadic 492301728 (-29 : Int), dyadic 417812064 (-29 : Int), dyadic 744910208 (-29 : Int), dyadic 381213056 (-29 : Int), dyadic (-928505152 : Int) (-29 : Int), dyadic (-212403888 : Int) (-29 : Int), dyadic 355494688 (-29 : Int), dyadic 390421632 (-29 : Int), dyadic (-7564613 : Int) (-29 : Int), dyadic (-535164736 : Int) (-29 : Int), dyadic 629362240 (-29 : Int), dyadic 800548608 (-29 : Int), dyadic 128209248 (-29 : Int), dyadic (-183429344 : Int) (-29 : Int), dyadic (-564945856 : Int) (-29 : Int), dyadic 970443456 (-29 : Int)] } : Tensor ℚ)),
    ("P", ({ shape := [2, 4], data := #[dyadic 43644160 (-26 : Int), dyadic (-95167208 : Int) (-26 : Int), dyadic (-10047267 : Int) (-26 : Int), dyadic (-33241596 : Int) (-26 : Int), dyadic 31266822 (-26 : Int), dyadic (-47960336 : Int) (-26 : Int), dyadic 17274342 (-26 : Int), dyadic (-42102780 : Int) (-26 : Int)] } : Tensor ℚ)),
    ("U", ({ shape := [4, 8], data := #[dyadic 79638064 (-28 : Int), dyadic (-290635264 : Int) (-28 : Int), dyadic 294191520 (-28 : Int), dyadic (-258318272 : Int) (-28 : Int), dyadic 410565312 (-28 : Int), dyadic (-381007520 : Int) (-28 : Int), dyadic 182078688 (-28 : Int), dyadic 221042496 (-28 : Int), dyadic 377861824 (-28 : Int), dyadic (-170013120 : Int) (-28 : Int), dyadic 128888776 (-28 : Int), dyadic 67493256 (-28 : Int), dyadic 178058016 (-28 : Int), dyadic (-169515808 : Int) (-28 : Int), dyadic (-308853408 : Int) (-28 : Int), dyadic (-322534272 : Int) (-28 : Int), dyadic (-318568512 : Int) (-28 : Int), dyadic 210100512 (-28 : Int), dyadic 186003616 (-28 : Int), dyadic (-155489120 : Int) (-28 : Int), dyadic 195505552 (-28 : Int), dyadic 20605358 (-28 : Int), dyadic 99427744 (-28 : Int), dyadic (-285201216 : Int) (-28 : Int), dyadic (-60216616 : Int) (-28 : Int), dyadic (-14610827 : Int) (-28 : Int), dyadic (-197631696 : Int) (-28 : Int), dyadic (-173568608 : Int) (-28 : Int), dyadic 303286016 (-28 : Int), dyadic 391439776 (-28 : Int), dyadic 225954608 (-28 : Int), dyadic 267692864 (-28 : Int)] } : Tensor ℚ)),
    ("WK", ({ shape := [4, 4], data := #[dyadic (-83543912 : Int) (-29 : Int), dyadic (-406638080 : Int) (-29 : Int), dyadic (-242765040 : Int) (-29 : Int), dyadic (-89333464 : Int) (-29 : Int), dyadic (-708162752 : Int) (-29 : Int), dyadic 137260448 (-29 : Int), dyadic (-241597072 : Int) (-29 : Int), dyadic 140187520 (-29 : Int), dyadic (-16756691 : Int) (-29 : Int), dyadic (-133295552 : Int) (-29 : Int), dyadic (-3769127 : Int) (-29 : Int), dyadic (-63486668 : Int) (-29 : Int), dyadic (-1083853824 : Int) (-29 : Int), dyadic 805626496 (-29 : Int), dyadic 923320320 (-29 : Int), dyadic 817117248 (-29 : Int)] } : Tensor ℚ)),
    ("WO", ({ shape := [4, 4], data := #[dyadic 25334322 (-25 : Int), dyadic 37692264 (-25 : Int), dyadic (-44538140 : Int) (-25 : Int), dyadic (-48314300 : Int) (-25 : Int), dyadic (-11772785 : Int) (-25 : Int), dyadic 48055848 (-25 : Int), dyadic (-41495544 : Int) (-25 : Int), dyadic (-37488788 : Int) (-25 : Int), dyadic 24847632 (-25 : Int), dyadic 28521778 (-25 : Int), dyadic 29183980 (-25 : Int), dyadic (-43318300 : Int) (-25 : Int), dyadic 61787296 (-25 : Int), dyadic 12438093 (-25 : Int), dyadic 7403088 (-25 : Int), dyadic 53428848 (-25 : Int)] } : Tensor ℚ)),
    ("WQ", ({ shape := [4, 4], data := #[dyadic 27509872 (-25 : Int), dyadic (-12317677 : Int) (-25 : Int), dyadic (-5064691 : Int) (-25 : Int), dyadic (-13854884 : Int) (-25 : Int), dyadic (-53610512 : Int) (-25 : Int), dyadic 56075804 (-25 : Int), dyadic 34072032 (-25 : Int), dyadic 53567588 (-25 : Int), dyadic 10401778 (-25 : Int), dyadic (-21899714 : Int) (-25 : Int), dyadic (-48513812 : Int) (-25 : Int), dyadic (-24615288 : Int) (-25 : Int), dyadic 17342592 (-25 : Int), dyadic 17022528 (-25 : Int), dyadic 41762776 (-25 : Int), dyadic 23744310 (-25 : Int)] } : Tensor ℚ)),
    ("WV", ({ shape := [4, 4], data := #[dyadic 192845472 (-27 : Int), dyadic 103001904 (-27 : Int), dyadic 205865792 (-27 : Int), dyadic 150967760 (-27 : Int), dyadic 37102764 (-27 : Int), dyadic 125364016 (-27 : Int), dyadic (-9091851 : Int) (-27 : Int), dyadic 128873112 (-27 : Int), dyadic (-199654528 : Int) (-27 : Int), dyadic (-212112688 : Int) (-27 : Int), dyadic 114842024 (-27 : Int), dyadic 125337752 (-27 : Int), dyadic (-60722504 : Int) (-27 : Int), dyadic (-179188336 : Int) (-27 : Int), dyadic (-245559984 : Int) (-27 : Int), dyadic 212746112 (-27 : Int)] } : Tensor ℚ)),
    ("#const0", ({ shape := [], data := #[dyadic 1 (-1 : Int)] } : Tensor ℚ))]

/-- The task, as `taskByName` builds it for this input shape. -/
def task : Task := minTask 2 8

/-- The certificate of a scored submission, as the manifest gives it (0 numbers); a checker reads
    it through `CostM.cert`. -/
def cert : Cert := #[]

/-- The number of inputs the candidate claims the network answers correctly. -/
def claimedCount : Nat := 64

/-- What a candidate has to prove: the network answers at least `claimedCount` of its
    64 inputs correctly, in the sense of `Spec.lean`. -/
def Target : Prop := claimedCount ≤ numCorrect graph weights task

end Protected.N_attn_min2_tiny_v8d4_s1_c64
