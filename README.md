# Compact Proof Library

Compact proofs of the performance of small trained networks, written in Lean 4 and proved once for a
whole family of networks, at every size. Each entry is a checker in the counted language of the open
lane, with theorems that say what it certifies and what it costs. An instance is one trained network:
the kernel evaluates the checker on its weights, and the entry's theorems turn the result into a
proof about that network.

The specification is CompactCheck's, pinned to commit `56f82f2` of
[Auto-Research-Compact-Proof-in-Lean](https://github.com/WFJKK/Auto-Research-Compact-Proof-in-Lean):
`Correct` and `numCorrect` in `Spec.lean`, the exact evaluator, and the counted language
(`CountedOps.lean`, policy v4, where a checker reads the shape and the length of a weight for free).
The entries prove theorems about those definitions, never about copies of them. Lean 4.35.0-rc4, Mathlib v4.35.0-rc4; every theorem depends on the standard axioms
only (`propext`, `Classical.choice`, `Quot.sound`).

## Entries and instances

An entry's theorems hold for every size and every choice of weights. They say three things:

* soundness: the checker never certifies more inputs than the network answers correctly;
* cost: the checker's bill, as a formula in the sizes;
* count: which inputs the checker certifies, as a condition on the weights.

The cost is the same for every network of the same sizes. The count is not: two networks of the
same sizes can answer any number of inputs correctly, depending on their trained weights. So a
number of certified inputs comes from an instance: the kernel evaluates the checker on one network's
weights, and soundness turns that into the open lane's target, "at least N inputs correct", at the
length the cost formula gives.

| entry | method | networks | pipeline baseline |
| --- | --- | --- | --- |
| 1, `LinearMaxK/` | an exact test for each group of inputs with the same largest token | linear max-of-k, every `k`, `V`, `d` | 03, contract and interval, for every `k` |
| 2, `BruteForce/` | one forward pass on every input | every network and task (see the note in entry 2) | 01, brute force |
| 3, `LinearMaxKPlans/` | entry 1's test on chosen pieces of groups | linear max-of-k, every `k`, `V`, `d` | 03 with splitting, 04 with a budget |
| 4, `Symmetry/` | one forward pass per sorted input, weighted by its reorderings | networks that sum their input over the positions first (see the note in entry 2) | 02, symmetry |

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
  while the certified counts were measured with `lake exe measure`, the same checker compiled, at
  the previous pin. That checker also ran the network on the input with `V - 1` at every position
  and certified nothing if the answer was wrong; on these networks it was right, so by
  `check_billed` the counts are the same without it.
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

The kernel cannot evaluate the checker on a `V = 64` network in one `decide`: the checker's 307,009
charged operations, in exact rational arithmetic, ran out of memory at 8 GB. `Table.lean` splits the evaluation into
small statements. The weights of an exported network are integers times a power of two, one exponent
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

A note on which networks: soundness holds for every graph, but at the pinned CompactCheck a forward
pass can be billed only on graphs of `input`, `sum`, `linear` and `add` nodes (`singleCost`). On
any other network, attention networks among them, the run fails and certifies nothing. The same
holds for entry 4.

### Instances

| network | k | V | d | certified | bill | length | checked by |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `max2_tiny-v8-s0` | 2 | 8 | 4 | 64 | 4,032 | 4,112 | kernel; accepted and scored |

The receipt is in `instances/receipts/BruteForce/`: description size 378 of a budget of 8,512.

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
| `LinearMaxKPlans/Pieces.lean` | pieces of groups: membership, sizes, valid plans |
| `LinearMaxKPlans/Checker.lean` | entry 3's checker |
| `LinearMaxKPlans/Runs.lean` | what it computes, and what it costs |
| `LinearMaxKPlans/Sound.lean` | soundness |
| `LinearMaxKPlans/Exact.lean` | exactness, the bill, the plan of whole groups |
| `Symmetry/Sorted.lean` | sorted inputs, how many there are, and the reorderings of an input |
| `Symmetry/Checker.lean` | entry 4's checker, its soundness, its count and its bill |
| `Symmetry/MaxK.lean` | symmetry on the linear max-of-k family: exact, and its bill |
| `instances/` | protected modules, instances, network files, receipts |
| `Measure.lean` | `lake exe measure`: entry 1's checker on exported networks, compiled |
| `scripts/make_candidate.py` | packages an instance for the acceptance service |
| `scripts/make_table_instance.py` | writes a kernel-checked instance of entry 1 for a large network |

## Build

    lake exe cache get          # Mathlib's prebuilt files
    lake build                  # the entries and the instances; every proof is checked
    lake build measure          # optional: the measuring tool

The `max2-v64-s0` instance takes about 4 minutes and 3 GB; everything else takes seconds.

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
the counted language (`Counted`, `CountedCheck`, `CountedOps`), which says what each operation is
charged. Nothing in this library has to be trusted: it proves theorems about those definitions.

An instance is about the weights in its protected module (`instances/Protected/`), the network's float
weights as exact dyadic rationals. CompactCheck's `scripts/make_protected.py` writes the module from
the network file; the acceptance service writes it itself and checks it against the network file
with the checker's own reader.

## Next

* A proof shorter than the hand-written one: the decoupled column test the agent found in the
  open-lane pilot (`Full64`: a pair passes if `top_a - M[m,a] < dm_m`, with `top_a` the largest
  entry of column `a` and `dm_m` the diagonal margin of column `m`), for every `k`, `V`, `d`.
* Gross et al.'s hand-written proofs for the attention max-of-k transformer, which need the counted
  language's bounds on `exp` and `softmax`.
* Kernel-checked instances of entry 1 for the other development seeds and for `V = 128`, with
  `scripts/make_table_instance.py` (at `V = 128` the table is four times larger and, by a count of
  operations, the kernel's work about ten times; not measured).
* Networks with `k = 3, 4`: entry 1's cost does not grow with `k`.
