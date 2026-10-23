import CompactCheck.Json
import CompactCheck.Spec
import CompactCheck.Counted

/-!
# Protected target: network `attn_max2_tiny-v8d4-s1`, claimed count 64

Written by scripts/make_protected.py from a network file of scripts/export_network.py. Not to be edited:
the acceptance service generates it, and checks its constants against the file with the checker's reader.
-/

namespace Protected.N_attn_max2_tiny_v8d4_s1_c64

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
    ("E", ({ shape := [8, 4], data := #[dyadic (-28689568 : Int) (-29 : Int), dyadic 697359424 (-29 : Int), dyadic (-143746800 : Int) (-29 : Int), dyadic 533738016 (-29 : Int), dyadic (-125197880 : Int) (-29 : Int), dyadic 667874880 (-29 : Int), dyadic (-468312192 : Int) (-29 : Int), dyadic (-12229315 : Int) (-29 : Int), dyadic 728461440 (-29 : Int), dyadic 509325088 (-29 : Int), dyadic 466184064 (-29 : Int), dyadic (-421141536 : Int) (-29 : Int), dyadic 60027760 (-29 : Int), dyadic 291933792 (-29 : Int), dyadic (-604073088 : Int) (-29 : Int), dyadic (-627007360 : Int) (-29 : Int), dyadic 361759296 (-29 : Int), dyadic 244607648 (-29 : Int), dyadic 544790400 (-29 : Int), dyadic 492620864 (-29 : Int), dyadic 195450784 (-29 : Int), dyadic (-502545696 : Int) (-29 : Int), dyadic (-364707168 : Int) (-29 : Int), dyadic (-649413952 : Int) (-29 : Int), dyadic (-296628736 : Int) (-29 : Int), dyadic (-469244480 : Int) (-29 : Int), dyadic 313766304 (-29 : Int), dyadic (-233312384 : Int) (-29 : Int), dyadic (-153807232 : Int) (-29 : Int), dyadic (-362156480 : Int) (-29 : Int), dyadic 527772864 (-29 : Int), dyadic 540357248 (-29 : Int)] } : Tensor ℚ)),
    ("P", ({ shape := [2, 4], data := #[dyadic 47797908 (-27 : Int), dyadic (-52099152 : Int) (-27 : Int), dyadic (-37251752 : Int) (-27 : Int), dyadic 9449075 (-27 : Int), dyadic 183838304 (-27 : Int), dyadic (-28313662 : Int) (-27 : Int), dyadic 35158508 (-27 : Int), dyadic (-61278996 : Int) (-27 : Int)] } : Tensor ℚ)),
    ("U", ({ shape := [4, 8], data := #[dyadic (-203952000 : Int) (-28 : Int), dyadic (-385970080 : Int) (-28 : Int), dyadic 208867312 (-28 : Int), dyadic (-157625936 : Int) (-28 : Int), dyadic 234009936 (-28 : Int), dyadic 30467536 (-28 : Int), dyadic 174284272 (-28 : Int), dyadic 237193680 (-28 : Int), dyadic 295081056 (-28 : Int), dyadic 273062592 (-28 : Int), dyadic 253928896 (-28 : Int), dyadic 228293456 (-28 : Int), dyadic 215818288 (-28 : Int), dyadic (-81244424 : Int) (-28 : Int), dyadic (-372941344 : Int) (-28 : Int), dyadic (-297512768 : Int) (-28 : Int), dyadic 205228160 (-28 : Int), dyadic 116285248 (-28 : Int), dyadic 296267360 (-28 : Int), dyadic (-234250576 : Int) (-28 : Int), dyadic 271739776 (-28 : Int), dyadic (-312975008 : Int) (-28 : Int), dyadic (-230345056 : Int) (-28 : Int), dyadic 135055744 (-28 : Int), dyadic 426534656 (-28 : Int), dyadic 3636091 (-28 : Int), dyadic (-234361664 : Int) (-28 : Int), dyadic (-149042320 : Int) (-28 : Int), dyadic 357730432 (-28 : Int), dyadic (-142554416 : Int) (-28 : Int), dyadic 102839616 (-28 : Int), dyadic 320184576 (-28 : Int)] } : Tensor ℚ)),
    ("WK", ({ shape := [4, 4], data := #[dyadic (-96029912 : Int) (-29 : Int), dyadic (-141028112 : Int) (-29 : Int), dyadic 272978880 (-29 : Int), dyadic 226635216 (-29 : Int), dyadic (-916388288 : Int) (-29 : Int), dyadic 941071616 (-29 : Int), dyadic 170528864 (-29 : Int), dyadic 1049886464 (-29 : Int), dyadic (-19614946 : Int) (-29 : Int), dyadic (-337033696 : Int) (-29 : Int), dyadic 354707200 (-29 : Int), dyadic (-169226176 : Int) (-29 : Int), dyadic (-437687488 : Int) (-29 : Int), dyadic (-329811008 : Int) (-29 : Int), dyadic 559982016 (-29 : Int), dyadic (-12693637 : Int) (-29 : Int)] } : Tensor ℚ)),
    ("WO", ({ shape := [4, 4], data := #[dyadic (-25108694 : Int) (-24 : Int), dyadic 23555258 (-24 : Int), dyadic 17202222 (-24 : Int), dyadic (-20647894 : Int) (-24 : Int), dyadic (-19661488 : Int) (-24 : Int), dyadic 20269314 (-24 : Int), dyadic (-17714384 : Int) (-24 : Int), dyadic (-22725584 : Int) (-24 : Int), dyadic 22385326 (-24 : Int), dyadic (-13483781 : Int) (-24 : Int), dyadic (-15226879 : Int) (-24 : Int), dyadic (-20954300 : Int) (-24 : Int), dyadic 15682746 (-24 : Int), dyadic 16007389 (-24 : Int), dyadic 24358794 (-24 : Int), dyadic 14838730 (-24 : Int)] } : Tensor ℚ)),
    ("WQ", ({ shape := [4, 4], data := #[dyadic 730656256 (-29 : Int), dyadic (-724997952 : Int) (-29 : Int), dyadic 70929768 (-29 : Int), dyadic (-511370272 : Int) (-29 : Int), dyadic 297058240 (-29 : Int), dyadic 479594848 (-29 : Int), dyadic (-623167680 : Int) (-29 : Int), dyadic (-119198720 : Int) (-29 : Int), dyadic (-235749520 : Int) (-29 : Int), dyadic (-172707488 : Int) (-29 : Int), dyadic 130693624 (-29 : Int), dyadic 13069767 (-29 : Int), dyadic (-103333608 : Int) (-29 : Int), dyadic 658024640 (-29 : Int), dyadic 272527488 (-29 : Int), dyadic 580109504 (-29 : Int)] } : Tensor ℚ)),
    ("WV", ({ shape := [4, 4], data := #[dyadic 26597754 (-25 : Int), dyadic 9807040 (-25 : Int), dyadic 25428766 (-25 : Int), dyadic 39394704 (-25 : Int), dyadic 43992600 (-25 : Int), dyadic 32239670 (-25 : Int), dyadic (-57580072 : Int) (-25 : Int), dyadic 43384224 (-25 : Int), dyadic (-39977196 : Int) (-25 : Int), dyadic (-50491452 : Int) (-25 : Int), dyadic 14693427 (-25 : Int), dyadic 35294520 (-25 : Int), dyadic (-9631467 : Int) (-25 : Int), dyadic (-42978820 : Int) (-25 : Int), dyadic (-63769224 : Int) (-25 : Int), dyadic 47337612 (-25 : Int)] } : Tensor ℚ)),
    ("#const0", ({ shape := [], data := #[dyadic 1 (-1 : Int)] } : Tensor ℚ))]

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

end Protected.N_attn_max2_tiny_v8d4_s1_c64
