# Compact Proof Library

Compact proofs of the performance of small trained networks, written in Lean 4 and proved once for a
whole family of networks, at every size. Each entry is a checker in the counted language of the open
lane, with theorems that say what it certifies and what it costs. An instance is one trained network:
the kernel evaluates the checker on its weights, and the entry's theorems turn the result into a
proof about that network.

The specification is CompactCheck's, pinned to commit `c11b8e4` of
[Auto-Research-Compact-Proof-in-Lean](https://github.com/WFJKK/Auto-Research-Compact-Proof-in-Lean):
`Correct` and `numCorrect` in `Spec.lean`, the exact evaluator, and the counted language
(`CountedOps.lean`, version 4). The entries prove theorems about those definitions, never about
copies of them. Lean 4.35.0-rc4, Mathlib v4.35.0-rc4; every theorem depends on the standard axioms
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
| 2, `BruteForce/` | one forward pass on every input | every network and task | 01, brute force |

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

Before that it runs the network once, on the guard input with `V - 1` at every position, and gates
every group's count on the answer. The counted language cannot read the length of a weight tensor,
and a forward pass that succeeds shows the weights have the sizes their shapes say. If the pass fails
or the answer is wrong, the checker certifies nothing. The guard input lies in the last group, so
the gate loses nothing when that group is answered correctly.

### The theorems

`check_sound` holds for every graph of the family and all weights. The other theorems assume, in
addition, well-formed weights (`WF` in `Family.lean`): `E`, `L` and `U` are present, with the shapes
`[d, V]`, `[d, d]`, `[V, d]` and as many entries as their shapes say.

* `check_sound` (`Sound.lean`): for every graph of the family, all weights and all certificates, the
  count is at most `numCorrect`. The soundness theorem of an instance, `D_sound`, which the open
  lane's acceptance service asks for at the protected graph, is this theorem specialised.
* `check_billed` (`Exact.lean`): the count is exactly the sum of `(m + 1)^k - m^k` over the groups
  the network answers entirely correctly, if it answers the guard input correctly, and 0 otherwise;
  the bill is `bill k V d`.
* `groupOk_iff`: for a group `m < V`, the tests pass iff the network answers every input of the
  group correctly. The test is exact, not only sufficient.
* `check_complete`: a network that answers all `V^k` inputs correctly is certified on all of them.
* `check_bill`: the bill depends on the sizes `(k, V, d)` only.
* `bill_eq`: the bill in closed form, the sum of

  | part | operations |
  | --- | --- |
  | the guard's forward pass | `k d + d² + d V + V - 1` |
  | the columns of `M` | `V (d² + V d)` |
  | the constant `k - 1` | `1` |
  | the tests and their gates | `(V - 1) V (V + 3) + V` |

The bill does not depend on the values of the weights: the counted language cannot branch on a truth
value, so the cost is a property of the method. Apart from the guard it does not depend on `k`
either, while brute force (entry 2) grows as `V^k`.

### Instances

| network | k | V | d | certified | correct | bill | length | brute force |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `max2_tiny-v8-s0` | 2 | 8 | 4 | 64 | 64 | 1,072 | 1,152 | 4,112 |
| `max2-v64`, 6 development seeds | 2 | 64 | 8 | 4,095 or 4,092 | the same | 307,728 | 308,816 | 2,683,968 |
| `max2-v128`, 6 development seeds | 2 | 128 | 16 | 16,383 | 16,383 | 2,427,040 | 2,431,392 | 40,358,144 |

* What is proved: for the tiny network, everything in its row; it is the kernel-checked instance
  `instances/LinearMaxKInstances/Max2Tiny.lean`. For the others, the bill and the length (they follow
  from `check_billed` and `bill_eq` for every well-formed network of these sizes), while the certified
  counts are measured with `lake exe measure`, the same checker compiled.
* The length is the bill plus the number of weight entries, which the open lane charges once for
  extracting the weights. The brute force column is entry 2's length on the same network,
  `V^k (k d + d² + d V + V - 1)` plus the same extraction. (The zoo's `B` for these networks,
  2,696,387 and 40,407,555, is defined a little differently.)
* `correct` is the zoo's exact count of correct inputs. On every development network the checker
  certifies all of them: the inputs these networks get wrong fill whole groups (the group of the token
  0, or the groups of the tokens 0 and 1).
* The tiny instance proves the target of the protected module, and the acceptance service accepted
  and scored it: receipt in `instances/receipts/LinearMaxK/`, description size 4,285 of a budget of
  8,512, general layer replayed in 0.6 s.
* A single `decide +kernel` over the 300,000 charged operations of a `V = 64` instance ran out of
  memory here (8 GB; the acceptance service allows 12 GB), so a kernel-checked instance at that size
  is to be split into many small theorems; that is the next step.

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

On networks beyond linear maps the single-input rule encloses `exp` and `softmax` in rational bounds
instead of computing them, so it could miss an input answered correctly by a tiny margin; the count
stays sound.

### Instances

| network | k | V | d | certified | bill | length | checked by |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `max2_tiny-v8-s0` | 2 | 8 | 4 | 64 | 4,032 | 4,112 | kernel; accepted and scored |

The receipt is in `instances/receipts/BruteForce/`: description size 378 of a budget of 8,512.

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
| `BruteForce/Checker.lean` | entry 2's checker, its soundness and its bill, for every network |
| `BruteForce/MaxK.lean` | brute force on the linear max-of-k family: exact, and its bill |
| `instances/` | protected modules, instances, network files, receipts |
| `Measure.lean` | `lake exe measure`: entry 1's checker on exported networks, compiled |
| `scripts/make_candidate.py` | packages an instance for the acceptance service |

## Build

    lake exe cache get          # Mathlib's prebuilt files
    lake build                  # the entries and the instances; every proof is checked
    lake build measure          # optional: the measuring tool

## Submitting an instance to the acceptance service

    python3 scripts/make_candidate.py instances/LinearMaxKInstances/Max2Tiny.lean <dir> \
        --model tests/max2_tiny --network max2_tiny-v8-s0 --claimed 64 --bill 1072
    # then, in a checkout of the Lean repository at the pinned commit:
    python3 scripts/accept.py submit <dir> --repo <pipeline repository> --work <work dir>

The script copies the instance and the library modules it imports under `Candidate/`, as the service
requires, and writes the manifest of a scored submission. The service compiles them in a sandbox,
replays every constant through the kernel, checks that the checker uses only the counted language,
and has the kernel accept the soundness theorem and the instance theorem at the statements it builds
itself.

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

* Kernel-checked instances of entry 1 at `V = 64`, split into theorems per row of `M` and per group.
* Plans (the pipeline's baselines 03 with splitting and 04 with a budget): entry 1's exact test on
  chosen pieces of groups, sound for every plan, with the bill a function of the plan.
* Symmetry (baseline 02): one forward pass per sorted input, weighted by its number of permutations.
* Networks with `k = 3, 4`: apart from the guard, entry 1's cost does not grow with `k`.
