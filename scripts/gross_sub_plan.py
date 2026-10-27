#!/usr/bin/env python3
"""Plans and certificates of entry 9 (Gross et al.'s sub-cubic proofs) for one network.

    python gross_sub_plan.py <gbmi checkout> <pipeline repo> <model folder> <network id> \\
        <network.json> <out dir> [config substring]

For each of their 100 configurations (`LargestWrongLogitQuadraticConfig`) whose name contains the
substring, runs their code on the network (`gbmi` at fb5b181: their directions, their search for
`min_gaps`, their proof for its count) and writes `<out dir>/<network id>--<configuration>.json`:

    err, eu    the method codes of `GrossSub.check`
    gaps       their min_gaps, by ranks of the query, the largest token and the number of positions
               holding another token (the checker's plan)
    cert       the certificate, as exact `p/q` strings
    theirs     the count their code certifies

for `lake exe measure_sub <network.json> <plans...>`. A plan already written is skipped, so a run
that stops can be resumed. Needs torch, transformer_lens (below 3) and numpy; the model is built as
the pipeline's results/gross-cubic-2026-10-16/run_all_proofs.py builds it (for the min tasks the
vocabulary reversed, so that the network computes a max, as their code assumes).

Certificate layout (`GrossSub.check`): `p̄` (d numbers), `μ` (d), the averages (2 V n: endpoint,
rank of the largest token, number of other positions), then the method's numbers (`errCertLen`).
Token-indexed vectors are in the network's own token order. Every number is dyadic, as the counted
language's `exp` needs: floats are rounded to multiples of 2^-30, and the `svd` method's matrices
are found in floats and then checked exactly, as the checker will check them.
"""
from __future__ import annotations

import json
import math
import sys
import time
from fractions import Fraction
from pathlib import Path

import numpy as np
import torch

K_ROUND = 30  # resolution of the certificate's numbers: 2^-30

ERR = {"svd": 0, "max_diff": 1, "mean+max_diff": 1, "max_diff_exact": 2, "exact_EQKE+max_diff_exact": 3,
       "max_diff_subproduct": 4, "mean+max_diff_subproduct": 4, "max_diff_subproduct_recursive": 5,
       "mean+max_diff_subproduct_recursive": 5, "mean_recursive+max_diff_subproduct_recursive": 5}
EU = {"mean_query+max_diff": 0, "svd_query+max_diff": 0, "max_diff": 0, "max_diff_exact": 1,
      "global_max_diff_exact": 2}


def build(repo: Path, model: str, nid: str, reverse: bool):
    """The network as a TransformerLens model (attention only, no biases), float64."""
    from transformer_lens import HookedTransformer, HookedTransformerConfig
    z = np.load(repo / model / "zoo" / f"{nid}.npz")
    W = {k: torch.tensor(z[k], dtype=torch.float64) for k in z.files}
    E, P, WQ, WK, WV, WO, U = (W[k] for k in ("E", "P", "WQ", "WK", "WV", "WO", "U"))
    if reverse:
        E, U = E.flip(0), U.flip(1)
    V, d = E.shape
    n = P.shape[0]
    h = WQ.shape[1]
    cfg = HookedTransformerConfig(n_layers=1, n_heads=1, d_model=d, d_head=h, n_ctx=n, d_vocab=V,
                                  d_vocab_out=V, attn_only=True, normalization_type=None,
                                  positional_embedding_type="standard", default_prepend_bos=False,
                                  device="cpu", dtype=torch.float64, seed=0)
    m = HookedTransformer(cfg)
    st = m.state_dict()
    st["embed.W_E"] = E
    st["pos_embed.W_pos"] = P
    st["blocks.0.attn.W_Q"] = WQ[None]
    st["blocks.0.attn.W_K"] = WK[None]
    st["blocks.0.attn.W_V"] = WV[None]
    st["blocks.0.attn.W_O"] = WO[None]
    for b in ("b_Q", "b_K", "b_V"):
        st[f"blocks.0.attn.{b}"] = torch.zeros(1, h, dtype=torch.float64)
    st["blocks.0.attn.b_O"] = torch.zeros(d, dtype=torch.float64)
    st["unembed.W_U"] = U
    st["unembed.b_U"] = torch.zeros(V, dtype=torch.float64)
    m.load_state_dict(st)
    m.eval()
    return m


# ---------------------------------------------------------------- dyadic numbers and exact algebra

def dy(x, k=K_ROUND) -> Fraction:
    return Fraction(int(round(float(x) * (1 << k))), 1 << k)


def dyv(xs, k=K_ROUND) -> list[Fraction]:
    return [dy(x, k) for x in np.asarray(xs, dtype=float).reshape(-1)]


def fstr(q: Fraction) -> str:
    return f"{q.numerator}/{q.denominator}"


def load_exact(path):
    """The network file's weights as exact rationals."""
    j = json.load(open(path))
    W = {}
    for w in j["weights"]:
        e = w["exp"]
        sc = Fraction(1, 1 << -e) if e < 0 else Fraction(1 << e)
        W[w["name"]] = (w["shape"], [Fraction(i) * sc for i in w["ints"]])
    return W, j["task"]


def mat(W, name):
    shape, vals = W[name]
    r, c = shape
    return [[vals[i * c + k] for k in range(c)] for i in range(r)]


def mmul(A, B):
    Bt = list(zip(*B))
    return [[sum((a * b for a, b in zip(row, col)), Fraction(0)) for col in Bt] for row in A]


def tr(A):
    return [list(r) for r in zip(*A)]


def dominant(X, F) -> bool:
    """The checker's `psdOk`: `X - F Fᵀ` has `2 D_ii ≥ Σ_(j ≠ i) |D_ij| + |D_ji|`."""
    r = len(X)
    FF = mmul(F, tr(F))
    D = [[X[i][j] - FF[i][j] for j in range(r)] for i in range(r)]
    return all(sum(abs(D[i][j]) + abs(D[j][i]) for j in range(r) if j != i) <= D[i][i] + D[i][i]
               for i in range(r))


# ---------------------------------------------------------------- their certificate numbers

def factors(Eq, Ek, WQs, WK):
    """The two factors their FactoredMatrix reduces `Eq W_Q W_Kᵀ Ekᵀ` to."""
    d, h = WQs.shape
    if h < d:
        return Eq @ WQs, WK.T @ Ek.T
    return Eq @ (WQs @ WK.T), Ek.T


def certificate(method, Eq, Ek, WQs, WK, dirs):
    """The directions and mean rows their code uses for an error method (floats)."""
    c = {}
    if method in ("svd", "max_diff", "mean+max_diff", "max_diff_exact"):
        A, B = factors(Eq, Ek, WQs, WK)
        U_, S_, Vh_ = np.linalg.svd(A @ B)
        c["u"], c["v"] = U_[:, 0], Vh_[0, :]
        if method == "mean+max_diff":
            Ar = A - np.outer(c["u"], c["u"] @ A)
            c["mean0"] = Ar.mean(axis=0)
    elif "subproduct" in method:
        for k in ("kd", "qd", "skd", "sqd", "qu", "ku"):
            v = np.asarray(dirs[k], dtype=float).reshape(-1)
            c[k] = v / np.linalg.norm(v)
        if method.startswith("mean"):
            qd, sqd, qu, ku = (c[k] for k in ("qd", "sqd", "qu", "ku"))
            Qe = Eq - np.outer(qd, qd @ Eq)
            Qe2 = Qe - np.outer(sqd, sqd @ Qe)
            Wqe = WQs - np.outer(qu, qu @ WQs)
            Wke = WK - np.outer(ku, ku @ WK)
            m0, m1, m2 = Qe2, Wqe, Wke.T
            if method.startswith("mean_recursive"):
                c["mean0"], c["mean1"], c["mean2"] = m0.mean(axis=0), m1.mean(axis=0), m2.mean(axis=0)
            elif method == "mean+max_diff_subproduct":
                c["mean0"] = m0.mean(axis=0)
                c["mean1"] = (m0 @ m1).mean(axis=0)
                c["mean2"] = (m0 @ m1 @ m2).mean(axis=0)
            else:
                c["mean0"] = m0.mean(axis=0)
    return c


def svd_cert(We, pbar, u, v):
    """`T`, `F₁`, `F₂`, `ε` of the `svd` bound, checked exactly as the checker checks them; `u`, `v`
    dyadic, in the network's token order."""
    E, Pm = mat(We, "E"), mat(We, "P")
    WQ, WK = mat(We, "WQ"), mat(We, "WK")
    c = We["#const0"][1][0]
    V, d = len(E), len(E[0])
    n = len(Pm)
    h = len(WQ[0])
    Eq = [[E[t][a] + Pm[n - 1][a] for a in range(d)] for t in range(V)]
    Ek = [[E[t][a] + pbar[a] for a in range(d)] for t in range(V)]
    Wq = [[WQ[a][k] * c for k in range(h)] for a in range(d)]
    if h < d:
        A = mmul(Eq, Wq)
        B = mmul(tr(WK), tr(Ek))
    else:
        A = mmul(Eq, mmul(Wq, tr(WK)))
        B = tr(Ek)
    r = len(A[0])
    uA = [sum((u[s] * A[s][k] for s in range(V)), Fraction(0)) for k in range(r)]
    Ar = [[A[q][k] - u[q] * uA[k] for k in range(r)] for q in range(V)]
    Bv = [sum((B[k][t] * v[t] for t in range(V)), Fraction(0)) for k in range(r)]
    Br = [[B[k][t] - Bv[k] * v[t] for t in range(V)] for k in range(r)]
    GA = mmul(tr(Ar), Ar)
    GB = mmul(Br, tr(Br))
    GAf = np.array(GA, dtype=float)
    GBf = np.array(GB, dtype=float)
    delta = 1e-9 * max(np.abs(GAf).max(), 1e-300)
    w_, Q_ = np.linalg.eigh(GAf + delta * np.eye(r))
    S = Q_ @ np.diag(np.sqrt(np.maximum(w_, delta))) @ Q_.T
    for _ in range(8):
        T = [[dy(S[i][j], 40) for j in range(r)] for i in range(r)]
        TT = mmul(T, tr(T))
        X1 = [[TT[i][j] - GA[i][j] for j in range(r)] for i in range(r)]
        Z = [[Fraction(0)] * r for _ in range(r)]
        if dominant(X1, Z):
            F1 = Z
            break
        X1f = np.array(X1, dtype=float)
        eta = 1e-3 * max(np.min(np.linalg.eigvalsh(X1f)), 0)
        try:
            Lc = np.linalg.cholesky(X1f - eta * np.eye(r))
            F1 = [[dy(Lc[i][j], 50) for j in range(r)] for i in range(r)]
            if dominant(X1, F1):
                break
        except np.linalg.LinAlgError:
            pass
        delta *= 10
        w_, Q_ = np.linalg.eigh(GAf + delta * np.eye(r))
        S = Q_ @ np.diag(np.sqrt(np.maximum(w_, delta))) @ Q_.T
    else:
        raise RuntimeError("no certificate for T Tᵀ ⪰ Arᵀ Ar")
    Tf = np.array(T, dtype=float)
    Y = Tf.T @ GBf @ Tf
    lam = float(np.max(np.linalg.eigvalsh((Y + Y.T) / 2)))
    TGT = mmul(tr(T), mmul(GB, T))
    eta = 1e-7 * max(lam, 1e-300)
    for _ in range(8):
        eps = dy(math.sqrt(2 * (lam + 2 * eta)) * (1 + 1e-12), 40)
        if eps * eps < 2 * Fraction(lam):
            eps += Fraction(1, 1 << 40)
        X2 = [[(eps * eps if i == j else Fraction(0)) - 2 * TGT[i][j] for j in range(r)] for i in range(r)]
        X2f = np.array(X2, dtype=float)
        try:
            Lc = np.linalg.cholesky(X2f - eta * np.eye(r))
            F2 = [[dy(Lc[i][j], 50) for j in range(r)] for i in range(r)]
            if dominant(X2, F2):
                return T, F1, F2, eps
        except np.linalg.LinAlgError:
            pass
        eta *= 10
    raise RuntimeError("no certificate for ε² I ⪰ 2 Tᵀ Br Brᵀ T")


# ---------------------------------------------------------------- the plans

def main() -> None:
    if len(sys.argv) < 7:
        sys.exit(__doc__)
    gbmi, repo, model, nid = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3], sys.argv[4]
    netjson, outdir = sys.argv[5], Path(sys.argv[6])
    filt = sys.argv[7] if len(sys.argv) > 7 else ""
    sys.path.insert(0, str(gbmi))
    import gbmi.exp_max_of_n.analysis.quadratic as analysis_quadratic
    import gbmi.exp_max_of_n.analysis.subcubic as analysis_subcubic
    import gbmi.exp_max_of_n.verification.quadratic as quadratic
    import gbmi.exp_max_of_n.verification.subcubic as subcubic
    from gbmi.exp_max_of_n.verification import LargestWrongLogitQuadraticConfig
    from gbmi.utils.dataclass import enumerate_dataclass_values

    outdir.mkdir(parents=True, exist_ok=True)
    We, task = load_exact(netjson)
    mx = task == "max"
    m = build(repo, model, nid, not mx)
    V, n = m.cfg.d_vocab, m.cfg.n_ctx
    d, h = m.cfg.d_model, m.cfg.d_head
    W = {k: v.detach().numpy().astype(np.float64) for k, v in
         dict(E=m.W_E, P=m.W_pos, WQ=m.W_Q[0, 0], WK=m.W_K[0, 0], U=m.W_U).items()}
    c_scale = float(We["#const0"][1][0])
    flip = (lambda xs: list(xs)) if mx else (lambda xs: list(reversed(xs)))
    W_EP_direction_kwargs, find_min_gaps_kwargs, dirs, _ = analysis_subcubic.find_proof_shared(m)
    dn = {"kd": dirs["key_direction"], "qd": dirs["query_direction"], "skd": dirs["second_key_direction"],
          "sqd": dirs["second_query_direction"], "qu": dirs["W_Q_U"], "ku": dirs["W_K_U"]}
    dn = {k: v.detach().numpy().astype(np.float64) for k, v in dn.items()}
    pbar_f = W["P"].mean(axis=0)
    pbar = dyv(pbar_f)
    for tricks in enumerate_dataclass_values(LargestWrongLogitQuadraticConfig):
        name = tricks.short_description()
        out = outdir / f"{nid}--{name}.json"
        if filt not in name or out.exists():
            continue
        t0 = time.time()
        min_gaps, _ = analysis_subcubic.find_min_gaps_with_EQKE(model=m, **find_min_gaps_kwargs, **dirs,
                                                                 tricks=tricks, record_time=True)
        W_EP_direction = analysis_quadratic.W_EP_direction_for_tricks(**W_EP_direction_kwargs, tricks=tricks)
        r = subcubic.verify_proof(m, W_EP_direction=W_EP_direction, **dirs, min_gaps=min_gaps, tricks=tricks,
                                  sanity_check=False, print_complexity=False, print_results=False)
        # their averages of the attention, per endpoint, largest token and number of other positions
        EQKE_qk, EQKE_pos_err, (eps_t, _) = subcubic.decompose_EQKE_error(m, **dirs, sanity_check=False,
                                                                           tricks=tricks)
        ext = quadratic.compute_extreme_right_attention_quadratic(EQKE_qk + 0.0, min_gap=min_gaps)
        if not hasattr(eps_t, "ndim"):
            eps_t = torch.tensor(eps_t)
        if eps_t.ndim < 1:
            eps_t = eps_t[None]
        ext = ext.clone()
        ext[0] -= eps_t[:, None, None]
        ext[1] += eps_t[:, None, None]
        soft = quadratic.compute_extreme_softmaxed_right_attention_quadratic(
            ext, EQKE_pos_err, min_gap=min_gaps, attn_scale=m.blocks[0].attn.attn_scale).detach().numpy()
        avg = np.zeros((2, V, n))
        if tricks.attention_handling == "mean_query+diff":
            for e in (0, 1):
                for mm in range(V):
                    for c in range(n):
                        col = soft[e, :, mm, c]
                        col = col[~np.isnan(col)]
                        avg[e, mm, c] = col.mean() if len(col) else 0.0
        errn = tricks.attention_error_handling
        Eq = W["E"] + W["P"][-1][None, :]
        Ek = W["E"] + pbar_f[None, :]
        cf = certificate(errn, Eq, Ek, c_scale * W["WQ"], W["WK"], dn)
        if tricks.EUPU_handling == "mean_query+max_diff":
            mu = Eq.mean(axis=0)
        elif tricks.EUPU_handling == "svd_query+max_diff":
            mu = W_EP_direction.detach().numpy().astype(np.float64)
        else:
            mu = np.zeros(d)
        cert = pbar + dyv(mu) + dyv(avg.reshape(-1))
        e = ERR[errn]
        rdim = h if h < d else d
        if e <= 2:
            u, v = flip(dyv(cf["u"])), flip(dyv(cf["v"]))
            cert += u + v
            if e == 0:
                T, F1, F2, epsq = svd_cert(We, pbar, u, v)
                cert += [x for row in T for x in row] + [x for row in F1 for x in row] + \
                    [x for row in F2 for x in row] + [epsq]
            elif e == 1:
                cert += dyv(cf["mean0"]) if "mean0" in cf else [Fraction(0)] * rdim
        elif e >= 4:
            for k in ("kd", "qd", "skd", "sqd"):
                cert += flip(dyv(cf[k]))
            cert += dyv(cf["qu"]) + dyv(cf["ku"])
            for k, dim in (("mean0", d), ("mean1", h), ("mean2", d)):
                cert += dyv(cf[k]) if k in cf else [Fraction(0)] * dim
        rec = {"network": nid, "config": name, "mx": mx, "err": e, "eu": EU[tricks.EUPU_handling],
               "gaps": min_gaps.long().numpy().tolist(), "cert": [fstr(q) for q in cert],
               "theirs": int(r["correct_count_lower_bound"]), "seconds": round(time.time() - t0, 1)}
        out.write_text(json.dumps(rec))
        print(name, rec["theirs"], len(cert), rec["seconds"], flush=True)


if __name__ == "__main__":
    main()
