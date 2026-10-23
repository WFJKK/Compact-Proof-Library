import CompactCheck.Json
import CompactCheck.Spec
import CompactCheck.Counted

/-!
# Protected target: network `attn_max4_tiny-v4d4-s0`, claimed count 256

Written by scripts/make_protected.py from a network file of scripts/export_network.py. Not to be edited:
the acceptance service generates it, and checks its constants against the file with the checker's reader.
-/

namespace Protected.N_attn_max4_tiny_v4d4_s0_c256

open CompactCheck

/-- The network's graph, operation by operation, as the file gives it. -/
def graph : Graph := {
  positions := 4
  values := 4
  nodes := [
    Op.input,
    Op.param "E",
    Op.matmul 0 1,
    Op.param "P",
    Op.binary BinOp.add 2 3,
    Op.index 4 [IndexItem.all, IndexItem.one 3],
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
    ("E", ({ shape := [4, 4], data := #[dyadic 23398108 (-26 : Int), dyadic 37495324 (-26 : Int), dyadic (-12890965 : Int) (-26 : Int), dyadic (-74217168 : Int) (-26 : Int), dyadic (-3655135 : Int) (-26 : Int), dyadic 72009544 (-26 : Int), dyadic 71861032 (-26 : Int), dyadic (-18391060 : Int) (-26 : Int), dyadic (-47008924 : Int) (-26 : Int), dyadic 28709838 (-26 : Int), dyadic (-70288328 : Int) (-26 : Int), dyadic (-32546450 : Int) (-26 : Int), dyadic (-64291956 : Int) (-26 : Int), dyadic (-70964152 : Int) (-26 : Int), dyadic (-45880672 : Int) (-26 : Int), dyadic 40986340 (-26 : Int)] } : Tensor ℚ)),
    ("P", ({ shape := [4, 4], data := #[dyadic 28040102 (-29 : Int), dyadic 117755760 (-29 : Int), dyadic (-311119712 : Int) (-29 : Int), dyadic 179844768 (-29 : Int), dyadic 79604472 (-29 : Int), dyadic 231325008 (-29 : Int), dyadic (-306544960 : Int) (-29 : Int), dyadic 284739616 (-29 : Int), dyadic (-263597232 : Int) (-29 : Int), dyadic (-30423156 : Int) (-29 : Int), dyadic (-134550464 : Int) (-29 : Int), dyadic (-41216996 : Int) (-29 : Int), dyadic (-334232736 : Int) (-29 : Int), dyadic 102411600 (-29 : Int), dyadic (-165808400 : Int) (-29 : Int), dyadic 9209377 (-29 : Int)] } : Tensor ℚ)),
    ("U", ({ shape := [4, 4], data := #[dyadic 29788200 (-26 : Int), dyadic 41185312 (-26 : Int), dyadic (-67321296 : Int) (-26 : Int), dyadic (-17103758 : Int) (-26 : Int), dyadic 65219008 (-26 : Int), dyadic 67939208 (-26 : Int), dyadic 8575251 (-26 : Int), dyadic (-50151124 : Int) (-26 : Int), dyadic (-35148772 : Int) (-26 : Int), dyadic 74979808 (-26 : Int), dyadic (-62656456 : Int) (-26 : Int), dyadic (-45583392 : Int) (-26 : Int), dyadic (-40051936 : Int) (-26 : Int), dyadic (-12795789 : Int) (-26 : Int), dyadic (-27744192 : Int) (-26 : Int), dyadic 53370152 (-26 : Int)] } : Tensor ℚ)),
    ("WK", ({ shape := [4, 4], data := #[dyadic (-36514124 : Int) (-25 : Int), dyadic (-42321808 : Int) (-25 : Int), dyadic 44073728 (-25 : Int), dyadic (-4165924 : Int) (-25 : Int), dyadic (-12344595 : Int) (-25 : Int), dyadic (-22940508 : Int) (-25 : Int), dyadic (-1390554 : Int) (-25 : Int), dyadic (-31084226 : Int) (-25 : Int), dyadic (-24501172 : Int) (-25 : Int), dyadic (-44483200 : Int) (-25 : Int), dyadic (-39979840 : Int) (-25 : Int), dyadic (-36148208 : Int) (-25 : Int), dyadic 46179912 (-25 : Int), dyadic 54363500 (-25 : Int), dyadic (-47620120 : Int) (-25 : Int), dyadic 25199382 (-25 : Int)] } : Tensor ℚ)),
    ("WO", ({ shape := [4, 4], data := #[dyadic 7097343 (-25 : Int), dyadic 42139764 (-25 : Int), dyadic 48972844 (-25 : Int), dyadic (-37130016 : Int) (-25 : Int), dyadic 24369030 (-25 : Int), dyadic 26240122 (-25 : Int), dyadic 37489376 (-25 : Int), dyadic (-30257782 : Int) (-25 : Int), dyadic 23334734 (-25 : Int), dyadic (-27308642 : Int) (-25 : Int), dyadic 29110266 (-25 : Int), dyadic 40001820 (-25 : Int), dyadic 32422420 (-25 : Int), dyadic 23767808 (-25 : Int), dyadic 15440190 (-25 : Int), dyadic (-19201872 : Int) (-25 : Int)] } : Tensor ℚ)),
    ("WQ", ({ shape := [4, 4], data := #[dyadic (-92749784 : Int) (-26 : Int), dyadic (-83553336 : Int) (-26 : Int), dyadic 39818048 (-26 : Int), dyadic (-93143464 : Int) (-26 : Int), dyadic 29975512 (-26 : Int), dyadic 69516416 (-26 : Int), dyadic (-61347132 : Int) (-26 : Int), dyadic 36595320 (-26 : Int), dyadic (-35627036 : Int) (-26 : Int), dyadic (-55114500 : Int) (-26 : Int), dyadic 39815160 (-26 : Int), dyadic (-75530552 : Int) (-26 : Int), dyadic (-50417336 : Int) (-26 : Int), dyadic (-14829573 : Int) (-26 : Int), dyadic 103931576 (-26 : Int), dyadic 51610620 (-26 : Int)] } : Tensor ℚ)),
    ("WV", ({ shape := [4, 4], data := #[dyadic 15880504 (-25 : Int), dyadic 12772555 (-25 : Int), dyadic 13233570 (-25 : Int), dyadic 19154538 (-25 : Int), dyadic 41281084 (-25 : Int), dyadic 51917000 (-25 : Int), dyadic (-43098856 : Int) (-25 : Int), dyadic 19474058 (-25 : Int), dyadic 32683656 (-25 : Int), dyadic 51951968 (-25 : Int), dyadic 48864276 (-25 : Int), dyadic 32901092 (-25 : Int), dyadic (-11447148 : Int) (-25 : Int), dyadic (-29950232 : Int) (-25 : Int), dyadic 50744572 (-25 : Int), dyadic (-29072046 : Int) (-25 : Int)] } : Tensor ℚ)),
    ("#const0", ({ shape := [], data := #[dyadic 1 (-1 : Int)] } : Tensor ℚ))]

/-- The task, as `taskByName` builds it for this input shape. -/
def task : Task := maxTask 4 4

/-- The certificate of a scored submission, as the manifest gives it (0 numbers); a checker reads
    it through `CostM.cert`. -/
def cert : Cert := #[]

/-- The number of inputs the candidate claims the network answers correctly. -/
def claimedCount : Nat := 256

/-- What a candidate has to prove: the network answers at least `claimedCount` of its
    256 inputs correctly, in the sense of `Spec.lean`. -/
def Target : Prop := claimedCount ≤ numCorrect graph weights task

end Protected.N_attn_max4_tiny_v4d4_s0_c256
