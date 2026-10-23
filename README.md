# Compact Proof Library

Compact proofs of the performance of small trained networks, written in Lean 4 and proved once for a
whole family of networks, at every size. Each entry is a checker in the counted language of the open
lane, with theorems that say what it certifies and what it costs. An instance is one trained network:
the kernel evaluates the checker on its weights, and the entry's theorems turn the result into a
proof about that network.

The specification is CompactCheck's, pinned to commit `6f369e4` of
[Auto-Research-Compact-Proof-in-Lean](https://github.com/WFJKK/Auto-Research-Compact-Proof-in-Lean):
`Correct` and `numCorrect` in `Spec.lean`, the exact evaluator, and the counted language
(`CountedOps.lean`, policy v7). A checker reads the shape and the length of a weight for free, and
has CompactCheck's general single rule `gsingle` for attention networks. Every entry uses only the
minimal knowledge condition: the base allowlist, none of the legacy lane's rules for groups of
inputs.
The entries prove theorems about those definitions, never about copies of them. Lean 4.35.0-rc4,
Mathlib v4.35.0-rc4; every theorem depends on the standard axioms only (`propext`,
`Classical.choice`, `Quot.sound`).

## Entries and instances

An entry's theorems hold for every size and every choice of weights. They say three things:

* soundness: the checker never certifies more inputs than the network answers correctly;
* cost: the checker's bill, as a formula in the sizes (and, for entries 3 and 5, the plan; for
  entry 2 on attention networks, the charge of one forward pass, which its instances compute);
* count: which inputs the checker certifies, as a condition on the weights.

The cost is the same for every network of the same sizes (and, for entries 3 and 5, the same plan).
The count is not: two networks of the
same sizes can answer any number of inputs correctly, depending on their trained weights. So a
number of certified inputs comes from an instance: the kernel evaluates the checker on one network's
weights, and soundness turns that into the open lane's target, "at least N inputs correct", at the
length the cost formula gives.

| entry | method | networks | pipeline baseline |
| --- | --- | --- | --- |
| 1, `LinearMaxK/` | an exact test for each group of inputs with the same largest token | linear max-of-k, every `k`, `V`, `d` | 03, contract and interval, for every `k` |
| 2, `BruteForce/` | one forward pass on every input | every network and task: `check` for linear networks, `checkGeneral` for attention | 01, brute force |
| 3, `LinearMaxKPlans/` | entry 1's test on chosen pieces of groups | linear max-of-k, every `k`, `V`, `d` | 03 with splitting, 04 with a budget |
| 4, `Symmetry/` | one forward pass per sorted input, weighted by its reorderings | networks that sum their input over the positions first: the linear ones, not the attention ones | 02, symmetry |
| 5, `LinearMaxKColumnMax/` | tests on column maxima of `M`, against all outputs at once | linear max-of-k, every `k`, `V`, `d` | none: an agent's open-lane proof (`Full64`), generalised |
| 6, `AttnClasses/` | path tables, margins, bounds on `exp`, one test per class of inputs | one-head attention, max or min of `n` tokens, every `n`, `V`, `d`, `h` | none; compare Gross et al.'s cubic proof |

## Entry 1: linear max-of-k (`LinearMaxK/`)

### The family

`k` positions, `V` tokens. The one-hot input is summed over the positions, then mapped by the
embedding `E` (`d × V`), a linear layer `L` (`d × d`) and the unembedding `U` (`V × d`), with no bias
and no nonlinearity. The label is the largest token. This is `models/max2/model.py` of the pipeline
with `n_ctx = k`; `IsLinearMaxK` recognises its exported graph.

Everything such a network computes is in the matrix `M = U L E`: the logits of an input are the sum
of the columns of `M` at its tokens (`eval_family`).

### The method

Group the inputs by their largest token `m`. For an output `j ≠ m`, write `D(t) = M[m,t] - M[j,t]`.
An input of the group has margin `Σ_{t ∈ x} D(t)` against `j`, one of its tokens is `m`, and the
others are at most `m`. So the worst input of the group against `j` puts `m` at one position and the
minimiser of `D` at the other `k - 1`, and every input of the group is answered correctly iff, for
every `j ≠ m`,

    D(m) + (k - 1) · min_{t ≤ m} D(t) > 0

The checker computes the columns of `M`, makes this test for every group and every other output, and
counts the groups that pass, `(m + 1)^k - m^k` inputs each. For `k = 2` this is the pipeline's
baseline 03: after the contraction to `M`, its interval leaf over the inputs `(t, m)` with `t ≤ m`
bounds each margin by exactly this minimum.

Before that it reads the shapes and the lengths of `E`, `L` and `U`, which cost nothing, and
certifies nothing unless they are `[d, V]`, `[d, d]`, `[V, d]` with `d V`, `d²` and `V d` entries.

### The theorems

`check_sound` holds for every graph of the family and all weights. The other theorems assume, in
addition, well-formed weights (`WF` in `Family.lean`): `E`, `L` and `U` are present, with the shapes
`[d, V]`, `[d, d]`, `[V, d]` and as many entries as their shapes say.

* `check_sound` (`Sound.lean`): for every graph of the family, all weights and all certificates, the
  count is at most `numCorrect`. The soundness theorem of an instance, `D_sound`, which the open
  lane's acceptance service asks for at the protected graph, is this theorem specialised.
* `check_billed` (`Exact.lean`): the count is exactly the sum of `(m + 1)^k - m^k` over the groups
  the network answers entirely correctly; the bill is `bill V d`.
* `groupOk_iff`: for a group `m < V`, the tests pass iff the network answers every input of the
  group correctly. The test is exact, not only sufficient.
* `check_complete`: a network that answers all `V^k` inputs correctly is certified on all of them.
* `check_bill`: the bill depends on `V` and `d` only.
* `bill_eq`: the bill in closed form, the sum of

  | part | operations |
  | --- | --- |
  | the columns of `M` | `V (d² + V d)` |
  | the constant `k - 1` | `1` |
  | the tests and their gates | `(V - 1) V (V + 3)` |

The bill does not depend on the values of the weights: the counted language cannot branch on a truth
value, so the cost is a property of the method. It does not depend on `k` either, while brute force
(entry 2) grows as `V^k`.

### Instances

| network | k | V | d | certified | correct | bill | length | brute force |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `max2_tiny-v8-s0` | 2 | 8 | 4 | 64 | 64 | 1,001 | 1,081 | 4,112 |
| `max2-v64-s0` | 2 | 64 | 8 | 4,095 | 4,095 | 307,009 | 308,097 | 2,683,968 |
| `max2-v64`, 5 other development seeds | 2 | 64 | 8 | 4,095 or 4,092 | the same | 307,009 | 308,097 | 2,683,968 |
| `max2-v128`, 6 development seeds | 2 | 128 | 16 | 16,383 | 16,383 | 2,424,449 | 2,428,801 | 40,358,144 |

* What is proved: in the first two rows, the certified count (the instance's target, at least
  that many inputs correct), the bill and the length. They are kernel-checked instances
  (`instances/LinearMaxKInstances/`), and the acceptance service accepted and scored both; the
  receipts are in `instances/receipts/LinearMaxK/`. For the other rows, the bill and the length
  (they follow from `check_billed` and `bill_eq` for every well-formed network of these sizes),
  while the certified counts are measured with `lake exe measure`, the same checker compiled.
* The length is the bill plus the number of weight entries, which the open lane charges once for
  extracting the weights. The brute force column is entry 2's length on the same network,
  `V^k (k d + d² + d V + V - 1)` plus the same extraction. (The zoo's `B` for these networks,
  2,696,387 and 40,407,555, is defined a little differently.)
* `correct` is the zoo's exact count of correct inputs, computed outside Lean. On every development
  network the checker certifies all of them: the inputs these networks get wrong fill whole groups
  (the group of the token 0, or the groups of the tokens 0 and 1). Exactness (`check_billed`) says
  the same in Lean, but no instance states the upper bound as a theorem.
* The receipts' description size is 4,303, of a budget of 8,512 for the tiny network and 12,544 for
  `max2-v64-s0`.

### Large instances

The kernel cannot evaluate the checker on a `V = 64` network in one `decide`: the checker's roughly
300,000 charged operations, in exact rational arithmetic, ran out of memory at 8 GB. `Table.lean`
splits the evaluation into small statements. The weights of an exported network are integers times a power of two, one exponent
per tensor, so `M = 2^e · MZ` for the integer matrix `MZ` of the mantissas, and every test has the
same outcome on `MZ` as on `M`. An instance then proves, each by its own `decide`, one theorem per row
of `MZ` and one per group's tests, and `check_billed_of_table` assembles them.
`scripts/make_table_instance.py` writes such an instance for any network of the family. The one for
`max2-v64-s0` compiles in about 4 minutes and 3 GB, one theorem at a time to stay within the
acceptance service's 12 GB; the service replays it in about 3.5 minutes.

## Entry 2: brute force (`BruteForce/`)

### The method

The single-input rule, one exact forward pass charged as `cost-v3` charges it, on every input of the
task's space, counting the inputs it answers correctly. It uses nothing about the network, so it is
written once for every graph and every task, and every other entry is measured against it.

### The theorems

* `check_sound` (`Checker.lean`): for every graph, task, weights and certificate, the count is at
  most `numCorrect`.
* `check_billed`: when a forward pass can be billed, at `s` operations, the count is the number of
  inputs the single-input rule passes, and the bill is `s` per input.
* `check_billed_maxK` (`MaxK.lean`): on the linear max-of-k family with well-formed weights, the count
  is exactly `numCorrect` and the bill is `V^k (k d + d² + d V + V - 1)`.

`check` bills a forward pass only on graphs of `input`, `sum`, `linear` and `add` nodes
(`singleCost`); on an attention network it fails. `checkGeneral` (`General.lean`) is the same
program with CompactCheck's general single rule `gsingle`: the general checker's exact forward
pass, `exp` and softmax enclosed in rational bounds, charged as `cost-v3` charges a `single` leaf
(and refused on linear networks, whose `linear` nodes it does not evaluate).

* `checkGeneral_sound`: for every graph, task, weights and certificate, the count is at most
  `numCorrect`.
* `countGSingles_run`: given each input's verdict and charge as a separate fact, the run of the
  checker. One `decide` over every forward pass of an attention network does not fit in the
  kernel's memory, so an instance proves one fact per input and puts them together with this
  lemma (`scripts/make_brute_general_instance.py` writes such an instance).

On the attention models every forward pass is charged the same,
`2 n d h + 2 d h + 4 n h + 2 n d + 2 n + d + V d + V - 1` with `n` positions and head size `h`
(191 on the tiny max-of-2 networks, 287 on the tiny max-of-4 ones). The formula is not proved:
the instances state the charge the kernel computes, and `lake exe measure_attn --bf` finds the
formula's value on every network of the four attention zoos' development sets.

### Instances

| network | k | V | d | certified | bill | length | checked by |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `max2_tiny-v8-s0` | 2 | 8 | 4 | 64 | 4,032 | 4,112 | kernel; accepted and scored |
| `attn_max2_tiny-v8d4-s1` | 2 | 8 | 4 | 64 | 12,224 | 12,360 | kernel, 64 facts; accepted and scored |
| `attn_min2_tiny-v8d4-s1` | 2 | 8 | 4 | 64 | 12,224 | 12,360 | kernel, 64 facts; accepted and scored |
| `attn_max4_tiny-v4d4-s0` | 4 | 4 | 4 | 256 | 73,472 | 73,584 | kernel, 256 facts; accepted and scored |
| `attn_min4_tiny-v4d4-s0` | 4 | 4 | 4 | 256 | 73,472 | 73,584 | kernel, 256 facts; accepted and scored |

The attention networks are the pipeline's tiny ones (`tests/attn_*_tiny`, head size `h = d = 4`),
the development seed of each. Their length counts the 136 or 112 weight entries, not the scale the
exporter adds as `#const0`, as the service counts them. The receipts are in
`instances/receipts/BruteForce/`: description size 378 for both checkers, of a budget of 8,512 or
more.

## Entry 3: plans (`LinearMaxKPlans/`)

### The method

A plan is a list of pieces `⟨m, lo, hi⟩`: the inputs whose largest token is `m` and whose smallest
token is in `[lo, hi]`. The checker makes entry 1's test on each piece instead of each group, and
counts the pieces that pass. For an output `j ≠ m`, the test of

* a tail, `hi = m` (the inputs of the group whose tokens are all at least `lo`), is

      D(m) + (k - 1) · min_{lo ≤ t ≤ m} D(t) > 0

* a band, `hi < m`, is the following, with `A` the minimum of `D` over `[lo, hi]` and `B` its
  minimum over `[lo, m]`:

      D(m) + A + (k - 2) · B > 0

The plan is public data, fixed with the checker. The checker first checks that it is valid: every
piece has `lo ≤ hi ≤ m < V`, and two pieces of one group have disjoint ranges. For an invalid plan it
certifies nothing.

The pipeline's other max-of-2 baselines are plans. Baseline 03 with its knob splits a group that
holds a wrong input into pieces (bands, and a tail at the top), down to a depth the knob sets; at
knob 1 the wrong inputs are isolated. Baseline 04 spends a budget: whole groups from the largest
token down, then one tail of the next group. The plan of all whole groups is entry 1, at one
operation more (`check_groups`).

### The theorems

* `check_sound` (`Sound.lean`): for every graph of the family, every plan, all weights and all
  certificates, the count is at most `numCorrect`.
* `check_billed` (`Exact.lean`): on well-formed weights and a valid plan, the count is the sum of
  the sizes of the pieces whose tests pass, and the bill is `billPlan V d plan`.
* `pieceOk_iff`: on well-formed weights, for a valid piece, when `k ≥ 2` or the piece is a tail,
  the tests pass iff the network answers every input of the piece correctly. The tests are exact.
* `countP_mem` (`Pieces.lean`): for `k ≥ 1`, a valid piece has `tailSize k m lo - tailSize k m (hi + 1)`
  inputs, where `tailSize k m a = (m + 1 - a)^k - (m - a)^k`.
* `billPlan` (`Runs.lean`): the columns as in entry 1, two literals, and for each piece
  `(V - 1) (c + 1)`, with `c = 2 (m - lo) + 3` for a tail and `2 (m - lo) + 4` for a band.
* `check_groups` (`Exact.lean`): on well-formed weights, the plan of all whole groups has entry 1's
  count, and entry 1's bill plus one.

### Instances

| network | plan | certified | bill | length | checked by |
| --- | --- | --- | --- | --- | --- |
| `max2_tiny-v8-s0` | baseline 04 at knob 0.75: `⟨7, 0, 7⟩`, `⟨6, 4, 6⟩` | 20 | 568 | 648 | kernel; accepted and scored |

The receipt is in `instances/receipts/LinearMaxKPlans/`: description size 5,524 of a budget of
8,512.

## Entry 4: symmetry (`Symmetry/`)

### The method

For a network that sums its one-hot input over the positions before anything else
(`symmetricNet`), and a task whose label does not depend on the order of the tokens, an input and
its reorderings are answered alike (CompactCheck's `singleOk_perm`). The checker runs the
single-input rule on the sorted inputs only, `(V + k - 1).choose k` of them, and counts each that
passes with its number of reorderings, `mult V k x`.

### The theorems

* `check_sound` (`Checker.lean`): for every such network, every such task whose input space is
  `k ≥ 1` positions of `V` tokens, all weights and all certificates, the count is at most
  `numCorrect`.
* `check_billed`: for the same networks and tasks, when a forward pass can be billed, at `s`
  operations, the count is the number of inputs the single-input rule passes, as for brute force,
  and the bill is `(V + k - 1).choose k · s`.
* `check_billed_maxK` (`MaxK.lean`): on the linear max-of-k family with well-formed weights, the count
  is exactly `numCorrect` and the bill is `(V + k - 1).choose k · (k d + d² + d V + V - 1)`.
* `countP_perm`, `length_sortedFrom` (`Sorted.lean`): `mult V k x` is the number of reorderings of
  `x`, and there are `(V - lo + k - 1).choose k` sorted inputs with tokens in `[lo, V)`.

### Instances

| network | k | V | d | certified | bill | length | checked by |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `max2_tiny-v8-s0` | 2 | 8 | 4 | 64 | 2,268 | 2,348 | kernel; accepted and scored |

The receipt is in `instances/receipts/Symmetry/`: description size 917 of a budget of 8,512. On a
`max2-v64` network the bill is 2,080 forward passes, 1,362,400 (length 1,363,488): about half of
brute force, as the pipeline's baseline 02 predicts.

Symmetry does not carry over to the attention models: they do not use their input only through a
sum over the positions (the positional embeddings, and the query read at the last position, make
the reorderings of an input different inputs to the network), and the pipeline's checker refuses
its symmetry rule there for that reason.

## Entry 5: column maxima (`LinearMaxKColumnMax/`)

### The method

The method of `Full64`, the proof an agent found in the open lane for the tiny network (pilot 2,
round 4), written for every `k`, `V`, `d` and every plan. Entry 1 tests each group against every
other output `j`, one test per `j`. Here each column `t` of `M` is summarised once:

| summary | value |
| --- | --- |
| `mx_t` | `max_{j ≠ t} M[j, t]`, the largest entry off the diagonal |
| `top_t` | `max (mx_t, M[t, t])`, the largest entry |
| `dm_t` | `M[t, t] - mx_t`, the margin of the diagonal |

No output gains more from token `t` than `top_t`, and no output other than `t` gains more than
`mx_t`. So one test of the summaries bounds the margins against all `j` at once.

A plan is a list of terms. Each certifies a set of inputs closed under reordering, given as a list of
sorted inputs, and counts their reorderings if its test passes. For inputs whose largest token is
`m`:

* `diag m`, the input `(m, ..., m)`: `0 < dm_m`.
* `box m lo hi dg`, the inputs whose other tokens all lie in `[lo, hi]`, with `hi < m`, and
  `(m, ..., m)` too if `dg`. With the loss `ℓ(t) = top_t - M[m, t]`, the test is

      (k - 1) · max_{lo ≤ t ≤ hi} ℓ(t) < dm_m

* `refined x`, the reorderings of the sorted input `x`, which holds `m` `c` times. Against every `j`
  that is not a token of `x`,

      Σ_{t ∈ x, t ≠ m} (mx_t - M[m, t]) < c · dm_m

  and against each other token `j` of `x`, its exact margin.
* `exact x`: the logits of `x`, the sum of the columns of its tokens, and one comparison of logit
  `m` with the largest of the others.

For `k = 2` these are `Full64`'s four tests: its `pair a m wd` is `box m a a wd`, its `rpair a m`
is `refined [a, m]`, its `exact a m` is `exact [a, m]`. The tests are sufficient, not exact: a box can
fail where every input is answered correctly, and then a refined or an exact test can take over.

The plan is public data, fixed with the checker. The checker checks it first: a box has
`lo ≤ hi < m < V`, the terms' sorted inputs are sorted inputs of the task, and none of them is in two
terms. For an invalid plan it certifies nothing.

### The theorems

* `check_sound` (`Sound.lean`): for every graph of the family, every plan, all weights and all
  certificates, the count is at most `numCorrect`.
* `check_billed`: on well-formed weights, `V > 0` and a valid plan, the count is the sum of the
  sizes of the terms whose tests pass, and the bill is `billPlan V k d plan`:

  | part | operations |
  | --- | --- |
  | the columns of `M` | `V (d² + V d)` |
  | their summaries | `V ((V - 2) + 2)` |
  | `diag m` | `1` |
  | `box m lo hi dg` | `2 (hi - lo) + (k - 2) + 2` |
  | `refined x` | `(2n - 1) + (c - 1) + 1 + u ((2n - 1) + (c - 1) + 3)`, with `n` tokens other than `m`, `u` of them distinct |
  | `exact x` | `(k - 1) V + (V - 2) + 1` |

  For `k = 2`: a box costs 2 per token of `[lo, hi]`, `refined [a, m]` costs 6, `exact [a, m]`
  costs `2V - 1`.

### Instances

| network | plan | certified | bill | length | checked by |
| --- | --- | --- | --- | --- | --- |
| `max2_tiny-v8-s0` | `Full64`'s | 64 | 581 | 661 | kernel; accepted and scored |

The plan is `Full64`'s, term for term: 2 diagonal tests, 16 boxes, 9 refined tests and 3 exact
tests. `Full64` certified the inputs `(6, 7)` and `(7, 6)` with the forward pass it ran to bound the
weights' lengths; since policy v4 the lengths are free, and `exact [6, 7]` certifies them. The
receipt is in `instances/receipts/LinearMaxKColumnMax/`: description size 7,404 of a budget of
8,512 (`Full64`'s own, written for this network only, was 7,502).

On the same network entry 1 certifies the same 64 inputs for a bill of 1,001 (length 1,081), so
entry 5 is 39% shorter. Every operation on the network's numbers is charged as in entry 1. The plan,
as in entry 3, is free structure in the checker, bounded by the description-size budget; here it
takes 661 of the 7,404. What the plan buys is the max rule: a pair costs one comparison against the
column summaries instead of one per other output.

At `V = 64` the plan is the open question. `scripts/column_max_plan.py` writes the cheapest passing
term for each input of `max2-v64-s0`: 766 boxes, 594 refined tests, 656 exact tests and one diagonal
test (`diag 13`). 62 diagonal inputs come with boxes; `(0, 0)`, which the network answers wrongly,
with none. Run in Lean with `#eval`, the checker certifies 4,095 inputs, entry 1's count, for a bill
of 129,369 (length 130,457) against entry 1's 307,009 (308,097). But that plan has 2,017 terms and a
description size of 63,693, against a budget of 12,544, so the service would refuse it: this is a
measurement, not a result the open lane would score. Whether a plan that fits the budget keeps much
of the gain is open; the per-pair choices alone carry about 3,200 bits. On the tiny network the
script writes `Full64`'s plan itself.

## Entry 6: one-head attention (`AttnClasses/`)

### The family

The pipeline's attention models (`models/attn-max2`, `attn-min2`, `attn-max4`, `attn-min4`, one
`model.py`): Gross et al.'s one-layer, one-head, attention-only transformer, with no biases and
learned positional embeddings. `n` positions, `V` tokens, width `d`, head size `h`. Each position's
residual is its token's embedding (`E`, `V × d`) plus its position's (`P`, `n × d`). The last
position `Q = n - 1` attends over every position with `W_Q` and `W_K` (`d × h`) at the scale `c`
(`h^(-1/2)` as a float, which the exporter writes as the constant `#const0`); the head reads the
values `W_V` (`d × h`) and writes back through `W_O` (`h × d`), and `U` (`d × V`) gives the logits.
The label is the largest token (`max`) or the smallest (`min`). `IsAttn` recognises the graph the
exporter writes, 26 operations, and `eval_attn` follows them over the reals.

On an input `x` with query token `q = x_Q` the logits are (`logit_eq`)

    logit_j = D[q, j] + Σ_p α_p O[x_p, p, j]

where `α` is the softmax over the positions of the scores `S[q, x_p, p]`, and the three path tables
are

| table | entry | what it is |
| --- | --- | --- |
| `D[q, j]` | `(E_q + P_Q) U` | the direct path of the query token |
| `O[t, p, j]` | `(E_t + P_p) W_V W_O U` | what token `t` at position `p` writes through the head |
| `S[q, t, p]` | `c (E_q + P_Q) W_Q · (E_t + P_p) W_K` | the score of token `t` at position `p` |

### The method

Let `ℓ` be the label and `j` any other output. The weights `α_p` are positive and add up to one, so

    logit_ℓ - logit_j ≥ Σ_p α_p H_p,   H_p = Dd[q, ℓ] + G[x_p, p, ℓ]

with the margins

    Dd[q, ℓ] = D[q, ℓ] - max_{j ≠ ℓ} D[q, j]
    G[t, p, ℓ] = O[t, p, ℓ] - max_{j ≠ ℓ} O[t, p, j]

Multiplied by the softmax's denominator, this says the input is answered correctly if

    Σ_p K(q, x_p, p, ℓ) > 0,   K = min (lo · H, hi · H)

where `lo ≤ exp S ≤ hi` are the counted language's bounds on `exp` (CompactCheck's `Exp.lean`, in
multiples of `2^-120`), so that `K ≤ exp(S) · H` whatever the sign of `H`.

The checker tests classes of inputs. Ranks order the tokens so that the label has the largest rank:
the token itself for `max`, `V - 1 - t` for `min`. A class fixes the query's rank, the label's
rank, the set `P` of the other positions that hold the label, and the largest rank `ρ'` at the
positions `R` left. Its test is

    K(q, q, Q, ℓ) + Σ_{p ∈ P} K(q, ℓ, p, ℓ) + Σ_{p ∈ R} m_p(ρ') > 0

with `m_p(ρ')` the least `K(q, t, p, ℓ)` over the tokens `t` of rank at most `ρ'`, a running
minimum. The query's position and the label's enter exactly, every other position through its
running minimum. The checker computes the tables once, tests every class, and keeps the verdicts in
a table. The count then looks up each input's class there: bookkeeping on public structure, which
the counted language does not charge, and which touches no number of the network.

The test is sufficient, not exact. It loses in two places: the margins take the worst other output
separately for the direct path and for each position; and each position in `R` is bounded by its
least term over all the ranks up to `ρ'`, whatever its own token, since the class fixes only the
largest rank in `R`, not which position holds it or what the others are. At `n = 2` the classes are
the inputs themselves (the query's rank, the label's rank and the other rank fix one input), and the
second loss applies only when the query holds the label. At `n = 4` the classes are far fewer than
the inputs: 8,416 for 65,536 at `V = 16`, and 528,256 for 16,777,216 at `V = 64`.

Gross et al.'s cubic proof, as the pipeline describes it (`results/gross-cubic-2026-10-16`),
pessimises once per query token, largest token, non-maximal token and number of copies of the
largest, and bounds the attention by a convexity argument: the head's output is a weighted average.
Here the positions are kept apart (the networks have positional embeddings, and `n` is small), and
the softmax is not bounded on its own: the test is on the sum of each position's `exp(S)` times its
margin, the numerator of the weighted average.

### The theorems

* `check_sound` (`Sound.lean`): for every graph of the family, the label `max` or `min`, all
  weights and all certificates, the count is at most `numCorrect`.
* `check_billed`: on well-formed weights (`Net.WF` in `Family.lean`: the seven matrices with their
  shapes and lengths, and the scale), when `exp` accepts every score (it refuses arguments of
  `2^12` or more, and numbers that are not dyadic), the count is the number of inputs whose class
  passes, and the bill is `bill V n d h` (`Check.lean`), the sum of

  | part | operations |
  | --- | --- |
  | queries and keys | `h d + V d + 2 V h d + n h d` |
  | scores, bounds on `exp` | `V² h + V n h + 4 V² n` |
  | paths through the head | `d² h + d² V + V² d + n V d` |
  | direct path | `V d + V² d` |
  | margins | `V (n + 1) (5V - 4)`, for `V ≥ 2` |
  | classes | `vtCost V n` |

  `vtCost V n` (`Runs.lean`) adds up, over the pairs of a query rank and a label rank `λ` at least
  as large: 4 operations for the query's term, and 4 for the label's term at each other position;
  `5λ - 1` per other position (`λ ≥ 1`) for its terms and their running minimum, when some class
  needs them; and per class one addition for each position in `R` and a comparison (the positions in
  `P` are added once per set `P`). For `n ≥ 3` it grows as `n 2^n V³`, while brute force runs `V^n`
  forward passes.
* `eval_attn`, `logit_eq`, `correct_of_bound` (`Family.lean`): the graph's real output is the formula
  above, and a positive sum makes the answer correct.

### Instances

| network | n | V | d = h | certified | bill | length | brute force | checked by |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `attn_max2_tiny-v8d4-s1` | 2 | 8 | 4 | 64 | 3,381 | 3,517 | 12,360 | kernel; accepted and scored |
| `attn_min2_tiny-v8d4-s1` | 2 | 8 | 4 | 64 | 3,381 | 3,517 | 12,360 | kernel; accepted and scored |
| `attn_max4_tiny-v4d4-s0` | 4 | 4 | 4 | 256 | 2,151 | 2,263 | 73,584 | kernel; accepted and scored |
| `attn_min4_tiny-v4d4-s0` | 4 | 4 | 4 | 256 | 2,151 | 2,263 | 73,584 | kernel; accepted and scored |

The tiny networks answer every input correctly, and the checker certifies all of them; brute force
is entry 2's length on the same network. The receipts are in `instances/receipts/AttnClasses/`:
description size 6,844 of a budget of 8,736 (`n = 2`) or 8,640 (`n = 4`).

### On the development networks

`lake exe measure_attn` runs the checker, compiled, on exported networks. On all 54 development
networks of the four zoos, `exp` accepted every score and the bill is `bill V n d h`. Six networks
per row, medians and the lowest; `share` is the share of the inputs the network answers correctly
that the proof certifies.

| task, size | d = h | bill | length | B / length | share: median, lowest | cubic proof: B / length | its share: median, lowest |
| --- | --- | --- | --- | --- | --- | --- | --- |
| max of 2, v64 | 32 | 766,241 | 774,497 | 45.9 | 98.3%, 96.5% | 6.3 | 99.1%, 98.1% |
| max of 2, v128 | 32 | 2,541,121 | 2,553,473 | 69.2 | 96.7%, 96.1% | 4.3 | 98.3%, 98.0% |
| min of 2, v64 | 32 | 766,241 | 774,497 | 45.9 | 98.7%, 98.2% | 6.3 | 99.2%, 99.0% |
| min of 2, v128 | 32 | 2,541,121 | 2,553,473 | 69.2 | 96.3%, 83.6% | 4.3 | 98.3%, 89.1% |
| max of 4, v16 | 8 | 66,323 | 66,867 | 974 | 99.7%, 98.9% | 223 | 99.5%, 98.9% |
| max of 4, v24 | 12 | 206,475 | 207,675 | 3,294 | 99.6%, 99.2% | 705 | 99.2%, 98.8% |
| max of 4, v64 | 32 | 3,497,795 | 3,506,115 | 62,982 | 97.7%, 97.3% | 12,283 | 97.5%, 96.8% |
| min of 4, v16 | 8 | 66,323 | 66,867 | 974 | 99.5%, 98.5% | 223 | 99.4%, 98.0% |
| min of 4, v24 | 12 | 206,475 | 207,675 | 3,294 | 99.7%, 99.5% | 705 | 99.5%, 99.4% |

* What is proved: the bill and the length, for every well-formed network of these sizes on which
  `exp` accepts every score (`check_billed`); the shares are measurements.
* `B` is the zoo's brute-force length, within 0.4% of entry 2's. The cubic proof's numbers are from
  the pipeline's run of Gross et al.'s code on the same networks (`results/gross-cubic-2026-10-16`).
  Its length is the pipeline's count of its operations (1 per multiply-add, addition or
  comparison, 3 per softmax entry, a small constant per inner loop), within a factor of about 2
  of any reasonable count, not a checked bill; its counts come from float arithmetic, checked only
  against the true number of correct inputs.
* At `n = 4` entry 6 is 4.4 to 5.1 times shorter than the cubic proof, and certifies more inputs on
  28 of the 30 networks (on the other two, at most 0.01 points fewer). At `n = 2` it is 7.2 to 16
  times shorter and certifies fewer on all 24, by 0.05 to 5.5 points. A class is one input there, so
  the gain over brute force is the path tables alone.
* On these networks neither certifies every correct input. The pipeline's hand-built `token_convex`
  proofs do, at `n = 4`: at `B/460` to `B/497` (v16), `B/1,766` to `B/1,818` (v24) and `B/14,836`
  (v64), 1.8 to 4.2 times longer than entry 6.

## Layout

| file | what it is |
| --- | --- |
| `Common/Basic.lean` | sums, and `Runs`: the value and the exact cost of a counted computation |
| `LinearMaxK/Family.lean` | the family: graph, well-formed weights, `M = U L E`, logits as sums of columns |
| `LinearMaxK/Groups.lean` | the groups: their sizes, and the partition of the inputs |
| `LinearMaxK/Checker.lean` | entry 1's checker, in the counted language |
| `LinearMaxK/Runs.lean` | what each part of the checker computes, and what it costs |
| `LinearMaxK/Sound.lean` | soundness |
| `LinearMaxK/Exact.lean` | exactness, completeness, the bill in closed form |
| `LinearMaxK/Table.lean` | the count from a table of integers, for instances too large for one `decide` |
| `BruteForce/Checker.lean` | entry 2's checker, its soundness and its bill, for every network |
| `BruteForce/MaxK.lean` | brute force on the linear max-of-k family: exact, and its bill |
| `BruteForce/General.lean` | brute force with the general single rule, for attention networks: soundness, and the run from one fact per input |
| `LinearMaxKPlans/Pieces.lean` | pieces of groups: membership, sizes, valid plans |
| `LinearMaxKPlans/Checker.lean` | entry 3's checker |
| `LinearMaxKPlans/Runs.lean` | what it computes, and what it costs |
| `LinearMaxKPlans/Sound.lean` | soundness |
| `LinearMaxKPlans/Exact.lean` | exactness, the bill, the plan of whole groups |
| `Symmetry/Sorted.lean` | sorted inputs, how many there are, and the reorderings of an input |
| `Symmetry/Checker.lean` | entry 4's checker, its soundness, its count and its bill |
| `Symmetry/MaxK.lean` | symmetry on the linear max-of-k family: exact, and its bill |
| `LinearMaxKColumnMax/Checker.lean` | entry 5's plans and checker |
| `LinearMaxKColumnMax/Runs.lean` | what it computes, and what it costs |
| `LinearMaxKColumnMax/Sound.lean` | soundness, and the count and the bill |
| `AttnClasses/Checker.lean` | entry 6's checker |
| `AttnClasses/Ops.lean` | the operations of the attention graph, over the reals |
| `AttnClasses/Family.lean` | the family: graph, well-formed weights, path tables, logits, the bound that makes an answer correct |
| `AttnClasses/Runs.lean` | what each part of the checker computes, and what it costs |
| `AttnClasses/Check.lean` | the whole run on well-formed weights: its count and its bill |
| `AttnClasses/Sound.lean` | soundness, and the count and the bill |
| `instances/` | protected modules, instances, network files, receipts |
| `Measure.lean` | `lake exe measure`: entry 1's checker on exported networks, compiled |
| `MeasureAttn.lean` | `lake exe measure_attn`: entry 6's checker on exported attention networks, compiled |
| `scripts/make_candidate.py` | packages an instance for the acceptance service |
| `scripts/make_table_instance.py` | writes a kernel-checked instance of entry 1 for a large network |
| `scripts/column_max_plan.py` | writes entry 5's plan for a max-of-2 network, and runs the checker on it |
| `scripts/make_brute_general_instance.py` | writes a kernel-checked instance of brute force on an attention network, one fact per input |

## Build

    lake exe cache get          # Mathlib's prebuilt files
    lake build                  # the entries and the instances; every proof is checked
    lake build measure          # optional: the measuring tools
    lake build measure_attn

The `max2-v64-s0` instance takes about 4 minutes and 3 GB. The instances of brute force on the
attention networks take about 2 minutes (64 forward passes) and 8 minutes (256) each, one
`decide` per forward pass; everything else takes seconds to a minute. With Mathlib and
CompactCheck built, the whole library and its instances build in about 17 minutes on two cores.

## Submitting an instance to the acceptance service

    python3 scripts/make_candidate.py instances/LinearMaxKInstances/Max2Tiny.lean <dir> \
        --model tests/max2_tiny --network max2_tiny-v8-s0 --claimed 64 --bill 1001
    # then, in a checkout of the Lean repository at the pinned commit:
    python3 scripts/accept.py submit <dir> --repo <pipeline repository> --work <work dir>

The script copies the instance and the library modules it imports under `Candidate/`, as the service
requires, and writes the manifest of a scored submission. The service compiles them in a sandbox,
replays every constant through the kernel, checks that the checker uses only the counted language,
and has the kernel accept the soundness theorem and the instance theorem at the statements it builds
itself. For a network of the zoo, `--model` is the model folder, `models/max2`.

## What has to be trusted

Lean's kernel and the definitions of CompactCheck's specification: `Spec.lean` and the files it rests
on (`Semantics`, `Eval`, `Network`, `Tensor`, `Task`, `Walk`). The statements about cost rest also on
the counted language (`Counted`, `CountedCheck`, `CountedGeneral`, `CountedOps`), which says what each
operation is charged. Nothing in this library has to be trusted: it proves theorems about those definitions.

An instance is about the weights in its protected module (`instances/Protected/`), the network's float
weights as exact dyadic rationals, and about the graph the module states. CompactCheck's
`scripts/export_network.py` writes the network file from the trained network (for the attention
models, the 26 operations of `model.py`'s forward pass), and `scripts/make_protected.py` writes the
module from the file; the acceptance service writes the module itself and checks it against the
network file with the checker's own reader. That the graph is the network's forward pass is the
exporter's claim, not a theorem.

## Next

* Entry 5 at `V = 64` within the description-size budget: a plan that fits (fewer, larger boxes,
  or a compact encoding of the per-pair choices, decoded by free code), then a kernel-checked
  instance with the tests on the integer table, as entry 1's large instances do.
* Entry 6 to every correct input: for the inputs of the classes that fail, a test of each input
  against each other output, from the same tables and bounds on `exp`. At `n = 2`, each input's
  own term at the other position instead of its running minimum, which is cheaper too (in a float
  prototype, 0 to 1.6 points more on the 24 two-token development networks, median 0.1).
* Entry 6 computes the bounds on `exp` at the query's position for every token, but reads them
  only for the query's own token: computing that one saves `4 V (V - 1)` operations, 2 to 3% at
  `n = 2` and 0.5 to 1.5% at `n = 4`.
* Kernel-checked instances of entry 6 at the zoo's sizes. They will need the evaluation split, as
  entry 1's `Table.lean` splits it: one `decide` over entry 1's run at `V = 64` already runs out
  of memory.
* Kernel-checked instances of entry 1 for the other development seeds and for `V = 128`, with
  `scripts/make_table_instance.py` (at `V = 128` the table is four times larger and, by a count of
  operations, the kernel's work about ten times; not measured).
* Networks with `k = 3, 4`: entry 1's cost does not grow with `k`, and an entry 5 box covers all
  the inputs of a group whose other tokens lie in its range with one test.
