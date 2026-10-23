#!/usr/bin/env python3
"""Write a kernel-checked instance of entry 1 (linear max-of-k) for a network too large for one `decide`.

    python3 scripts/make_table_instance.py <network.json> <Name> --lean-repo <CompactCheck checkout>

reads a network file of CompactCheck's scripts/export_network.py and writes

    instances/networks/<network>.json                the network file
    instances/Protected/N_<network>_c<count>.lean    the protected module, by CompactCheck's make_protected.py
    instances/LinearMaxKInstances/<Name>.lean        the instance

The instance proves the protected target through `LinearMaxK.check_billed_of_table`: the weights as
integer mantissas (checked against the protected weights by `rfl`), the rows of `MZ = U L E` (one
`decide +kernel` per row), the outcome of each group's tests (one `decide +kernel` per group), and the
guard's test on the table (one `decide +kernel`). This script computes the same numbers in Python, exactly,
to write them down; the kernel checks every one of them.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

LIB = Path(__file__).resolve().parent.parent
WIDTH = 100


def module_name(network_id: str, claimed: int) -> str:
    """As CompactCheck's make_protected.py names a protected module without a certificate."""
    return "N_" + re.sub(r"[^A-Za-z0-9]", "_", network_id) + f"_c{claimed}"


def lean_list(xs: list, indent: str) -> str:
    """A Lean list literal, wrapped to the line width."""
    items = [str(x) for x in xs]
    lines, cur = [], indent + "["
    for i, s in enumerate(items):
        piece = s + ("," if i < len(items) - 1 else "]")
        if len(cur) + len(piece) + 1 > WIDTH and cur.strip() != "[":
            lines.append(cur.rstrip())
            cur = indent + "  " + piece
        else:
            cur += ("" if cur.endswith("[") else " ") + piece
    lines.append(cur)
    return "\n".join(lines) if items else indent + "[]"


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("network", type=Path, help="a network file of scripts/export_network.py")
    ap.add_argument("name", help="the instance's name, e.g. Max2V64S0")
    ap.add_argument("--lean-repo", type=Path, required=True,
                    help="a checkout of Auto-Research-Compact-Proof-in-Lean at the pinned commit")
    args = ap.parse_args()

    net = json.loads(args.network.read_text())
    graph = net["graph"]
    k, V = graph["positions"], graph["values"]
    W = {w["name"]: w for w in net["weights"]}
    E, L, U = W["embedding.weight"], W["linear.weight"], W["unembedding.weight"]
    d = E["shape"][0]
    if E["shape"] != [d, V] or L["shape"] != [d, d] or U["shape"] != [V, d]:
        raise SystemExit("not a network of the linear max-of-k family")
    mE, mL, mU = E["ints"], L["ints"], U["ints"]

    # MZ = U L E over the integers, row by row, as rowZ computes it
    H = [[sum(mL[a * d + b] * mE[b * V + t] for b in range(d)) for a in range(d)] for t in range(V)]
    MZ = [[sum(mU[j * d + a] * H[t][a] for a in range(d)) for t in range(V)] for j in range(V)]

    def pair_ok(m: int, j: int) -> bool:
        dm = MZ[m][m] - MZ[j][m]
        mu = dm
        for t in range(m):
            mu = min(mu, MZ[m][t] - MZ[j][t])
        return 0 < dm + (k - 1) * mu

    groups = [all(j == m or pair_ok(m, j) for j in range(V)) for m in range(V)]
    guard = all(MZ[V - 1][V - 1] > MZ[j][V - 1] for j in range(V) if j != V - 1)
    if not guard:
        raise SystemExit("the network answers the guard input wrongly: the checker certifies nothing")
    count = sum((m + 1) ** k - m ** k for m in range(V) if groups[m])
    bill = (k * d + d * d + d * V + (V - 1)) + V * (d * d + V * d) + 1 + ((V - 1) * V * (V + 3) + V)

    prot = module_name(net["network"], count)
    (LIB / "instances" / "networks").mkdir(parents=True, exist_ok=True)
    shutil.copyfile(args.network, LIB / "instances" / "networks" / f"{net['network']}.json")
    out = subprocess.run([sys.executable, str(args.lean_repo / "scripts" / "make_protected.py"), str(args.network),
                          str(count), str(LIB / "instances")], capture_output=True, text=True)
    if out.returncode != 0 or out.stdout.strip() != prot:
        raise SystemExit(f"make_protected.py: {out.stdout} {out.stderr}")

    ns = f"LinearMaxKInstances.{args.name}"
    P = []
    P.append(f"import Protected.{prot}\nimport LinearMaxK.Table\n")
    P.append(f"""/-!
# Instance: entry 1 on `{net['network']}`

`k = {k}` positions, `V = {V}` tokens, width `d = {d}`. The protected module is the one the acceptance
service generates for a claim of {count}.

The kernel cannot evaluate the checker on these weights in one `decide`, so `D_instance` goes
through `LinearMaxK.check_billed_of_table`, in small steps that the kernel checks one by one:

* the weights are the integer mantissas `mE`, `mL`, `mU` times powers of two (`hE`, `hL`, `hU`,
  by `rfl`; the recursion limit is raised for these three, to unfold lists of hundreds of entries);
* the rows of `MZ = U L E` over the integers are the table `rows` (`row_0`, ..., one `decide` each);
* the tests of each group on the table come out as the list `outcomes` (`group_0`, ..., one
  `decide` each);
* the guard input is answered correctly, as the table shows (`guard`, one `decide`).

Written by `scripts/make_table_instance.py`.
-/
""")
    P.append(f"namespace {ns}\n\nopen CompactCheck LinearMaxK Protected.{prot}\n")
    P.append("""-- One theorem at a time: elaborated in parallel, the kernel's checks of the theorems below need
-- more address space than the acceptance service's sandbox allows (12 GB).
set_option Elab.async false
""")
    P.append("""/-- The checker on this network. -/
def D : Checker := fun I => check I graph task

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task :=
  fun w c n cost h => check_sound (g := graph) (by decide) w c n cost h
""")
    P.append("/-! ## The weights, as integer mantissas -/\n")
    for nm, m in (("mE", mE), ("mL", mL), ("mU", mU)):
        P.append(f"def {nm} : List ℤ :=\n{lean_list(m, '  ')}\n")
    for nm, key, w, shape in (("hE", "nE", E, f"[{d}, {V}]"), ("hL", "nL", L, f"[{d}, {d}]"),
                               ("hU", "nU", U, f"[{V}, {d}]")):
        e = w["exp"]
        P.append(f"set_option maxRecDepth 8192 in\n"
                 f"theorem {nm} : List.lookup {key} weights = some (dyadicTensor {shape} m{nm[1]} ({e})) := rfl\n")
    P.append("/-! ## The rows of `MZ = U L E`, one `decide` each -/\n")
    for j in range(V):
        P.append(f"def r{j} : List ℤ :=\n{lean_list(MZ[j], '  ')}\n")
    P.append("def rows : List (List ℤ) :=\n" + lean_list([f"r{j}" for j in range(V)], "  ") + "\n")
    for j in range(V):
        P.append(f"theorem row_{j} : rowZ mE mL mU {V} {d} {j} = r{j} := by decide +kernel\n")
    cases = "\n".join(f"  | {j}, _ => row_{j}.symm" for j in range(V))
    P.append(f"""theorem hrows : ∀ j < {V}, rows.getD j [] = rowZ mE mL mU {V} {d} j
{cases}
  | _ + {V}, h => absurd h (by omega)
""")
    P.append("/-! ## The tests of each group, one `decide` each -/\n")
    P.append("def outcomes : List Bool :=\n" + lean_list(["true" if b else "false" for b in groups], "  ") + "\n")
    for m in range(V):
        P.append(f"theorem group_{m} : groupOkZ rows {k} {V} {m} = {'true' if groups[m] else 'false'} := by decide +kernel\n")
    cases = "\n".join(f"  | {m}, _ => group_{m}" for m in range(V))
    P.append(f"""theorem hgroups : ∀ m < {V}, groupOkZ rows {k} {V} m = outcomes.getD m false
{cases}
  | _ + {V}, h => absurd h (by omega)
""")
    P.append(f"""/-! ## The guard, and the instance -/

theorem guard : guardOkZ rows {V} = true := by decide +kernel

theorem hEn : mE.length = {d} * {V} := by decide +kernel
theorem hLn : mL.length = {d} * {d} := by decide +kernel
theorem hUn : mU.length = {V} * {d} := by decide +kernel

theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some ({count}, {bill}) := by
  have h : CostM.billed (D Interp.counting) ⟨weights, cert⟩ =
      some (countZ rows {k} {V}, bill {k} {V} {d}) :=
    check_billed_of_table (g := graph) (by decide) hE hL hU hEn hLn hUn hrows guard cert
  rw [h, countZ_eq outcomes hgroups]
  decide +kernel

theorem performance : Target := by
  change claimedCount ≤ numCorrect graph weights task
  obtain ⟨cost, h⟩ := CostM.exec_of_billed D_instance
  exact D_sound weights cert {count} cost h

end {ns}
""")
    dst = LIB / "instances" / "LinearMaxKInstances" / f"{args.name}.lean"
    dst.write_text("\n".join(P))
    print(json.dumps({"instance": str(dst.relative_to(LIB)), "protected": prot, "count": count, "bill": bill,
                      "failed_groups": [m for m in range(V) if not groups[m]]}))


if __name__ == "__main__":
    main()
