#!/usr/bin/env python3
"""Write a kernel-checked instance of entry 9 (Gross et al.'s sub-cubic proofs) for one configuration.

    python3 scripts/make_sub_instance.py <network.json> <plan.json> <Name> --count <c> --bill <b>
        --lean-repo <CompactCheck checkout>

reads a network file of CompactCheck's scripts/export_network.py and a plan of entry 9 (one of their
configurations: the method codes `err`, `eu`, their gaps by ranks, and the certificate, as `p/q`
strings), and writes

    instances/certificates/<Name>.json                        the certificate, as make_protected.py and
                                                              make_candidate.py's --cert read it
    instances/Protected/N_<network>_c<count>_h<digest>.lean   the protected module with the certificate,
                                                              by CompactCheck's make_protected.py
    instances/GrossSubInstances/<Name>.lean                   the instance

`--count` and `--bill` are what `lake exe measure_sub` reports for the plan; the instance states them
and the kernel checks them (`D_instance`).
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import textwrap
from fractions import Fraction
from pathlib import Path

LIB = Path(__file__).resolve().parent.parent
WIDTH = 100


def canonical(cert: list[str]) -> list:
    """`p/q` strings as make_protected.py's canonical numbers: integers, or reduced [p, q] pairs."""
    out = []
    for s in cert:
        f = Fraction(s)
        out.append(f.numerator if f.denominator == 1 else [f.numerator, f.denominator])
    return out


def gaps_src(gaps: list, indent: str) -> str:
    """The gap table as a Lean list of lists of lists, one row of ranks of the largest token per line."""
    rows = []
    for rq, by_lam in enumerate(gaps):
        inner = ", ".join("[" + ", ".join(str(g) for g in cs) + "]" for cs in by_lam)
        line = indent + "  [" + inner + "]" + ("," if rq < len(gaps) - 1 else "]")
        rows.append(line)
    return indent + "[\n" + "\n".join(rows)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("network", type=Path)
    ap.add_argument("plan", type=Path)
    ap.add_argument("name")
    ap.add_argument("--count", type=int, required=True)
    ap.add_argument("--bill", type=int, required=True)
    ap.add_argument("--lean-repo", type=Path, required=True)
    ap.add_argument("--test", default=None, help="the pipeline's test folder, for the docstring")
    args = ap.parse_args()

    net = json.loads(args.network.read_text())
    plan = json.loads(args.plan.read_text())
    g = net["graph"]
    n, V = g["positions"], g["values"]
    d = next(w for w in net["weights"] if w["name"] == "E")["shape"][1]
    h = next(w for w in net["weights"] if w["name"] == "WQ")["shape"][1]
    mx = net["task"] == "max"
    err, eu = plan["err"], plan["eu"]
    cert = canonical(plan["cert"])

    cert_file = LIB / "instances" / "certificates" / f"{args.name}.json"
    cert_file.parent.mkdir(parents=True, exist_ok=True)
    cert_file.write_text(json.dumps(cert) + "\n")
    module = subprocess.run([sys.executable, str(args.lean_repo / "scripts" / "make_protected.py"),
                             str(args.network), str(args.count), str(LIB / "instances"), str(cert_file)],
                            check=True, capture_output=True, text=True).stdout.strip()

    label = "the largest token" if mx else "the smallest token"
    size = f"`n = {n}` positions, `V = {V}` tokens, width `d = {d}`, head size `h = {h}`"
    test = f"`{args.test}` of the pipeline, " if args.test else ""
    para1 = (f"{test}network `{net['network']}` (a development network): {size}. Gross et al.'s "
             f"configuration `{plan['config']}` (method codes `err = {err}`, `eu = {eu}`), with their "
             f"plan of gaps and the certificate of the protected module ({len(cert)} numbers).")
    para2 = (f"The kernel evaluates the checker on the protected weights and certificate "
             f"(`D_instance`): {args.count} of the {V ** n} inputs certified, for a bill of "
             f"{args.bill:,} (`GrossSub.subBill {err} {eu} gap {V} {n} {d} {h}`). The evaluation nests "
             f"deeper than Lean's default recursion limit allows the `decide` tactic, hence the option.")
    def wrap(t: str) -> str:
        """Wrap to the line width, never inside a code span."""
        parts = t.split("`")
        t = "`".join(p.replace(" ", "\u00a0") if i % 2 else p for i, p in enumerate(parts))
        lines = textwrap.wrap(t, width=WIDTH, break_long_words=False, break_on_hyphens=False)
        return "\n".join(lines).replace("\u00a0", " ")
    src = f"""import Protected.{module}
import GrossSub.Check

/-!
# Instance: entry 9 on the network `{net["network"]}`

{wrap(para1)}

{wrap(para2)}
-/

namespace GrossSubInstances.{args.name}

open CompactCheck GrossSub Protected.{module}

/-- Their plan of gaps, by the ranks of the query, of the largest token, and the number of positions
    holding a token other than the largest. -/
def gaps : List (List (List ℕ)) :=
{gaps_src(plan["gaps"], "  ")}

/-- The gap of a class (one where the plan has none). -/
def gap (rq lam c : ℕ) : ℕ := ((gaps.getD rq []).getD lam []).getD c 1

/-- The checker on this network: the label is {label}. -/
def D : Checker := fun I => check I {"true" if mx else "false"} {err} {eu} gap graph task

theorem graph_isAttn : AttnClasses.IsAttn graph := ⟨rfl, rfl, by decide, by decide⟩

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task :=
  fun w c n cost h => check_sound graph_isAttn {"true" if mx else "false"} {err} {eu} gap w c n cost h

set_option maxRecDepth 100000 in
theorem D_instance :
    CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some ({args.count}, {args.bill}) := by
  decide +kernel

theorem performance : Target := by
  change claimedCount ≤ numCorrect graph weights task
  obtain ⟨cost, h⟩ := CostM.exec_of_billed D_instance
  exact D_sound weights cert {args.count} cost h

end GrossSubInstances.{args.name}
"""
    out = LIB / "instances" / "GrossSubInstances" / f"{args.name}.lean"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(src)
    print(module)
    print(out)


if __name__ == "__main__":
    main()
