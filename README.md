# Disproof of the Aharoni–Korman Conjecture

The purpose of this repository is to formally verify Hollom's disproof of the Aharoni–Korman
conjecture, also known as the fishbone conjecture.

The [conjecture](https://link.springer.com/article/10.1007/BF00383948) states that every partially ordered set contains either
- an infinite antichain, or
- a chain C, and a partition of the whole partially ordered set into antichains such that each
  part meets C

In November 2024, Lawrence Hollom [disproved this conjecture](https://arxiv.org/abs/2411.16844).

The statement which has been formally proved can be found at the bottom of `AharoniKorman/Counterexample.lean`, and reads as follows:
```
theorem aharoni_korman_false :
    ¬ ∀ (α : Type) (_ : PartialOrder α),
        (∃ A : Set α, IsAntichain (· ≤ ·) A ∧ A.Infinite) ∨
        (∃ C : Set α, IsChain (· ≤ ·) C ∧
         ∃ S : Set (Set α), Setoid.IsPartition S ∧
          ∀ A ∈ S, IsAntichain (· ≤ ·) A ∧ (A ∩ C).Nonempty)
```

## Build the Lean files

To build the Lean files of this project, you need to have a working version of Lean.
See [the installation instructions](https://leanprover-community.github.io/get_started.html) (under Regular install).

To build the project, run `lake exe cache get` and then `lake build`.
