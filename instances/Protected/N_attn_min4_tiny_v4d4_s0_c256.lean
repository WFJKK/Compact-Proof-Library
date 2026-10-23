import CompactCheck.Json
import CompactCheck.Spec
import CompactCheck.Counted

/-!
# Protected target: network `attn_min4_tiny-v4d4-s0`, claimed count 256

Written by scripts/make_protected.py from a network file of scripts/export_network.py. Not to be edited:
the acceptance service generates it, and checks its constants against the file with the checker's reader.
-/

namespace Protected.N_attn_min4_tiny_v4d4_s0_c256

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
    ("E", ({ shape := [4, 4], data := #[dyadic 33358330 (-26 : Int), dyadic 47723732 (-26 : Int), dyadic (-70446744 : Int) (-26 : Int), dyadic (-70700352 : Int) (-26 : Int), dyadic 25913196 (-26 : Int), dyadic 50560844 (-26 : Int), dyadic (-22811890 : Int) (-26 : Int), dyadic 77110488 (-26 : Int), dyadic (-37128764 : Int) (-26 : Int), dyadic (-23556364 : Int) (-26 : Int), dyadic 35323960 (-26 : Int), dyadic 45686872 (-26 : Int), dyadic (-84634104 : Int) (-26 : Int), dyadic (-27222138 : Int) (-26 : Int), dyadic 10373329 (-26 : Int), dyadic (-33377352 : Int) (-26 : Int)] } : Tensor ℚ)),
    ("P", ({ shape := [4, 4], data := #[dyadic (-53260692 : Int) (-30 : Int), dyadic 334848736 (-30 : Int), dyadic 14640850 (-30 : Int), dyadic (-126139720 : Int) (-30 : Int), dyadic (-181417632 : Int) (-30 : Int), dyadic 476033568 (-30 : Int), dyadic (-12340507 : Int) (-30 : Int), dyadic 68603016 (-30 : Int), dyadic 148655264 (-30 : Int), dyadic 341505760 (-30 : Int), dyadic 381064448 (-30 : Int), dyadic (-348371488 : Int) (-30 : Int), dyadic (-375939552 : Int) (-30 : Int), dyadic 89640216 (-30 : Int), dyadic (-643361600 : Int) (-30 : Int), dyadic 553065536 (-30 : Int)] } : Tensor ℚ)),
    ("U", ({ shape := [4, 4], data := #[dyadic 39093420 (-27 : Int), dyadic (-58594852 : Int) (-27 : Int), dyadic (-82135696 : Int) (-27 : Int), dyadic 15149471 (-27 : Int), dyadic 122164120 (-27 : Int), dyadic 147039808 (-27 : Int), dyadic (-134871424 : Int) (-27 : Int), dyadic (-88482208 : Int) (-27 : Int), dyadic (-105360952 : Int) (-27 : Int), dyadic 54867912 (-27 : Int), dyadic 22161314 (-27 : Int), dyadic (-44594896 : Int) (-27 : Int), dyadic (-61658004 : Int) (-27 : Int), dyadic 93823744 (-27 : Int), dyadic 88517160 (-27 : Int), dyadic (-63081984 : Int) (-27 : Int)] } : Tensor ℚ)),
    ("WK", ({ shape := [4, 4], data := #[dyadic (-139903312 : Int) (-27 : Int), dyadic 209873264 (-27 : Int), dyadic 197529376 (-27 : Int), dyadic 220923248 (-27 : Int), dyadic (-56005796 : Int) (-27 : Int), dyadic 126993640 (-27 : Int), dyadic 148659632 (-27 : Int), dyadic 64074288 (-27 : Int), dyadic 124358880 (-27 : Int), dyadic (-113886408 : Int) (-27 : Int), dyadic (-102486656 : Int) (-27 : Int), dyadic (-83554408 : Int) (-27 : Int), dyadic 39108480 (-27 : Int), dyadic (-12384349 : Int) (-27 : Int), dyadic (-22460664 : Int) (-27 : Int), dyadic 22228280 (-27 : Int)] } : Tensor ℚ)),
    ("WO", ({ shape := [4, 4], data := #[dyadic (-44916524 : Int) (-27 : Int), dyadic 203198336 (-27 : Int), dyadic 87349256 (-27 : Int), dyadic 137299200 (-27 : Int), dyadic 92147496 (-27 : Int), dyadic 54113204 (-27 : Int), dyadic (-93236936 : Int) (-27 : Int), dyadic (-181568320 : Int) (-27 : Int), dyadic (-30899196 : Int) (-27 : Int), dyadic (-112078800 : Int) (-27 : Int), dyadic 85074464 (-27 : Int), dyadic 134135312 (-27 : Int), dyadic 110780960 (-27 : Int), dyadic (-5541471 : Int) (-27 : Int), dyadic (-162456688 : Int) (-27 : Int), dyadic (-180630240 : Int) (-27 : Int)] } : Tensor ℚ)),
    ("WQ", ({ shape := [4, 4], data := #[dyadic 5821423 (-24 : Int), dyadic (-20798252 : Int) (-24 : Int), dyadic (-18625138 : Int) (-24 : Int), dyadic (-28217010 : Int) (-24 : Int), dyadic (-16819140 : Int) (-24 : Int), dyadic 17312026 (-24 : Int), dyadic 10171864 (-24 : Int), dyadic 9506873 (-24 : Int), dyadic 13031937 (-24 : Int), dyadic (-14664583 : Int) (-24 : Int), dyadic (-9344856 : Int) (-24 : Int), dyadic (-17723924 : Int) (-24 : Int), dyadic (-13765902 : Int) (-24 : Int), dyadic 7745895 (-24 : Int), dyadic 14046044 (-24 : Int), dyadic 19436052 (-24 : Int)] } : Tensor ℚ)),
    ("WV", ({ shape := [4, 4], data := #[dyadic 108945888 (-26 : Int), dyadic 9182103 (-26 : Int), dyadic (-41077396 : Int) (-26 : Int), dyadic (-15584301 : Int) (-26 : Int), dyadic 73679992 (-26 : Int), dyadic 47178740 (-26 : Int), dyadic (-53353220 : Int) (-26 : Int), dyadic (-10762572 : Int) (-26 : Int), dyadic (-29577160 : Int) (-26 : Int), dyadic (-33972204 : Int) (-26 : Int), dyadic 74971368 (-26 : Int), dyadic (-12976767 : Int) (-26 : Int), dyadic 39028200 (-26 : Int), dyadic (-95825384 : Int) (-26 : Int), dyadic 49683344 (-26 : Int), dyadic (-84693496 : Int) (-26 : Int)] } : Tensor ℚ)),
    ("#const0", ({ shape := [], data := #[dyadic 1 (-1 : Int)] } : Tensor ℚ))]

/-- The task, as `taskByName` builds it for this input shape. -/
def task : Task := minTask 4 4

/-- The certificate of a scored submission, as the manifest gives it (0 numbers); a checker reads
    it through `CostM.cert`. -/
def cert : Cert := #[]

/-- The number of inputs the candidate claims the network answers correctly. -/
def claimedCount : Nat := 256

/-- What a candidate has to prove: the network answers at least `claimedCount` of its
    256 inputs correctly, in the sense of `Spec.lean`. -/
def Target : Prop := claimedCount ≤ numCorrect graph weights task

end Protected.N_attn_min4_tiny_v4d4_s0_c256
