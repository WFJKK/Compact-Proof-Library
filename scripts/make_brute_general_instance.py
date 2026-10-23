#!/usr/bin/env python3
"""Write a split kernel instance of brute force on a general (attention) network.

    python3 scripts/make_brute_general_instance.py <network.json> <protected module> <Name> <out.lean>

reads a network file of CompactCheck's scripts/export_network.py (an attention network of the
pipeline: the 26-operation graph of models/attn-*/model.py) and writes an instance module of
`BruteForce.checkGeneral` under the namespace `BruteForceInstances.<Name>`:

* one fact per input, `run1 x = some (true, K)`, each decided by the kernel on its own (one
  `decide +kernel` over all forward passes does not fit in the kernel's memory, CompactCheck's
  docs/COUNTED.md, "Split instances");
* `inputs_eq`: the input space as a list, decided by the kernel;
* `D_instance`, from the facts through `BruteForce.countGSingles_run`.

`K` is the charge of one forward pass, `2 n d h + 2 d h + 4 n h + 2 n d + 2 n + d + V d + V - 1`
(BruteForce/General.lean); the kernel checks every fact, so a wrong `K` or a wrong verdict only
makes the module fail to compile. The script asks the network file for nothing else: every input
is claimed to pass, which holds for networks that answer every input correctly (the tiny attention
networks of the pipeline); the script refuses others.
"""

from __future__ import annotations

import argparse
import itertools
import json
from fractions import Fraction
from pathlib import Path

import numpy as np


def forward_correct(net: dict) -> int:
    """How many inputs the network answers correctly, in floating point (a check, not a proof)."""
    W = {w["name"]: w for w in net["weights"]}

    def arr(name):
        w = W[name]
        vals = np.array([float(Fraction(i) * Fraction(2) ** w["exp"]) for i in w["ints"]])
        return vals.reshape(w["shape"]) if w["shape"] else vals.reshape(())

    E, P, WQ, WK, WV, WO, U = (arr(k) for k in ("E", "P", "WQ", "WK", "WV", "WO", "U"))
    c = float(arr("#const0"))
    g = net["graph"]
    n, V = g["positions"], g["values"]
    ok = 0
    for x in itertools.product(range(V), repeat=n):
        r = E[list(x)] + P
        q = (r[-1] @ WQ) * c
        s = (r @ WK) @ q
        a = np.exp(s - s.max())
        a /= a.sum()
        logits = (r[-1] + (a @ (r @ WV)) @ WO) @ U
        lab = max(x) if net["task"] == "max" else min(x)
        if np.argmax(logits) == lab and np.sum(logits == logits[lab]) == 1:
            ok += 1
    return ok


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("network", type=Path)
    ap.add_argument("protected")
    ap.add_argument("name")
    ap.add_argument("out", type=Path)
    args = ap.parse_args()

    net = json.loads(args.network.read_text())
    g = net["graph"]
    n, V = g["positions"], g["values"]
    W = {w["name"]: w for w in net["weights"]}
    d = W["E"]["shape"][1]
    h = W["WQ"]["shape"][1]
    K = 2 * n * d * h + 2 * d * h + 4 * n * h + 2 * n * d + 2 * n + d + V * d + V - 1
    inputs = [list(x) for x in itertools.product(range(V), repeat=n)]
    correct = forward_correct(net)
    if correct != len(inputs):
        raise SystemExit(f"{correct} of {len(inputs)} inputs correct: this script claims every input")

    def fact_name(x):
        return "in_" + "_".join(map(str, x))

    facts = "\n\n".join(
        f"theorem {fact_name(x)} : run1 {json.dumps(x)} = some (true, {K}) := by\n  decide +kernel"
        for x in inputs)
    inputs_lit = json.dumps(inputs).replace("],[", "], [")
    each = ", ".join(fact_name(x) for x in inputs)
    total = len(inputs)
    args.out.write_text(f"""import Protected.{args.protected}
import BruteForce.General

/-!
# Instance: brute force on the attention network `{net['network']}`

Written by `scripts/make_brute_general_instance.py`. `n = {n}` positions, `V = {V}` tokens, width
`d = {d}`, head size `h = {h}`: {total} inputs, each a forward pass of the general single rule charged
{K}. One fact per input, each decided by the kernel on its own; `D_instance` puts them together
(`BruteForce.countGSingles_run`): all {total} inputs certified, for a bill of {total} * {K} = {total * K:,}.
-/

namespace BruteForceInstances.{args.name}

open CompactCheck BruteForce Protected.{args.protected}

/-- Brute force with the general single rule on this network. -/
def D : Checker := fun I => checkGeneral I graph task

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task :=
  fun w c n cost h => checkGeneral_sound w c n cost h

/-- The general single rule's verdict and charge on input `x` of the protected weights. -/
abbrev run1 (x : Input) : Option (Bool × Nat) := gsingleOn weights graph task x

{facts}

-- A long list of inputs, and a long conjunction of facts, go deeper than the default limit.
set_option maxRecDepth 100000 in
theorem inputs_eq : allInputs task.space = {inputs_lit} := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem all_inputs : Each (fun x => run1 x = some (true, {K})) (allInputs task.space) := by
  rw [inputs_eq]
  exact ⟨{each}, trivial⟩

set_option maxRecDepth 100000 in
/-- The kernel never runs the whole checker at once: the instance follows from the facts. Every
    step rewrites with an equation, so the terms the kernel compares are identical. -/
theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some ({total}, {total * K}) := by
  obtain ⟨c', hrun, htot⟩ := countGSingles_run (g := graph) (task := task) ⟨weights, cert⟩ {K}
    (fun _ => true) (allInputs task.space) [] all_inputs
  have hlen : (allInputs task.space).length = {total} := by rw [inputs_eq]; rfl
  have hcount : (allInputs task.space).countP (fun _ => true) = {total} := by
    rw [List.countP_true, hlen]
  have htot' : c'.total = {total * K} := by
    rw [htot, hlen]
    simp [Cost.total]
  have hD : D Interp.counting = countGSingles Interp.counting graph task (allInputs task.space) := rfl
  rw [CostM.billed, CostM.exec, hD, hrun, hcount]
  simp only [Option.map_some, htot']

theorem performance : Target := by
  change claimedCount ≤ numCorrect graph weights task
  obtain ⟨cost, h⟩ := CostM.exec_of_billed D_instance
  exact D_sound weights cert {total} cost h

end BruteForceInstances.{args.name}
""")
    print(json.dumps({"network": net["network"], "inputs": total, "charge": K, "bill": total * K,
                      "out": str(args.out)}))


if __name__ == "__main__":
    main()
