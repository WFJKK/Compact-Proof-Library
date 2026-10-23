#!/usr/bin/env python3
"""Write entry 5's plan for a max-of-2 network, and a Lean file that runs the checker on it.

    python3 scripts/column_max_plan.py <network.json> <out.lean>
    lake env lean <out.lean>

reads a network file of CompactCheck's scripts/export_network.py (a linear max-of-k network with
k = 2) and writes <out.lean>: the plan, and a `#eval` that runs `LinearMaxKColumnMax.check` on the
network with the counting interpreter and prints whether the plan is valid and `(count, bill)`.

The plan is the cheapest term that passes, for each input, computed here in exact arithmetic: for a
pair `a < m` the box `box m a a` (2 operations), else the refined test (6), else the exact test
(`2V - 1`); for `(m, m)`, the first box of its group that passes (free: its test shows `dm_m > 0`),
else the diagonal test (1). An input no test certifies is left out. The script only chooses the
plan; the checker computes the count and the bill. This is a measurement, not a kernel-checked
instance.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("network", type=Path)
    ap.add_argument("out", type=Path)
    args = ap.parse_args()

    net = json.loads(args.network.read_text())
    graph = net["graph"]
    k, V = graph["positions"], graph["values"]
    if k != 2:
        raise SystemExit("this script writes plans for k = 2 only")
    W = {w["name"]: w for w in net["weights"]}

    def values(w: dict) -> list[Fraction]:
        return [Fraction(i) * Fraction(2) ** w["exp"] for i in w["ints"]]

    E, L, U = (values(W[n]) for n in ("embedding.weight", "linear.weight", "unembedding.weight"))
    d = W["embedding.weight"]["shape"][0]
    H = [[sum(L[a * d + b] * E[b * V + t] for b in range(d)) for a in range(d)] for t in range(V)]
    M = [[sum(U[j * d + a] * H[t][a] for a in range(d)) for t in range(V)] for j in range(V)]
    mx = [max(M[j][t] for j in range(V) if j != t) for t in range(V)]
    top = [max(mx[t], M[t][t]) for t in range(V)]
    dm = [M[t][t] - mx[t] for t in range(V)]

    terms = []
    for m in range(V):
        diag = dm[m] > 0  # (m, m) still to certify
        for a in range(m):
            if top[a] - M[m][a] < dm[m]:
                # a box that passes shows dm_m > 0, so it certifies (m, m) too, for free
                terms.append(f".box {m} {a} {a} {'true' if diag else 'false'}")
                diag = False
            elif mx[a] - M[m][a] < dm[m] and M[a][a] - M[m][a] < M[m][m] - M[a][m]:
                terms.append(f".refined [{a}, {m}]")
            else:
                s = [M[j][a] + M[j][m] for j in range(V)]
                if max(s[j] for j in range(V) if j != m) < s[m]:
                    terms.append(f".exact [{a}, {m}]")
        if diag:
            terms.append(f".diag {m}")

    net_path = args.network.resolve()
    args.out.write_text(f"""import CompactCheck.Json
import LinearMaxKColumnMax.Sound

/-! Entry 5 on `{net['network']}`: the cheapest passing term for each input. Written by
`scripts/column_max_plan.py`. -/

open CompactCheck LinearMaxKColumnMax

def plan : List LinearMaxKColumnMax.Term :=
  [{(","+chr(10)+"   ").join(terms)}]

def main : IO Unit := do
  let j ← readJson "{net_path}"
  match parseNetwork j with
  | .error e => IO.println s!"error {{e}}"
  | .ok net =>
    let g := net.graph
    IO.println s!"planOk {{planOk g.values g.positions plan}}"
    IO.println s!"{{repr (CostM.billed (check Interp.counting plan g (maxTask g.positions g.values))
      ⟨net.weights, #[]⟩)}}"

#eval main
""")
    print(json.dumps({"network": net["network"], "terms": len(terms), "out": str(args.out)}))


if __name__ == "__main__":
    main()
