# Classical strong subadditivity of subentropy

This repository contains a Lean 4 proof of Theorem 22 from [Quantum Subentropy: Subadditivity and Sharp Bounds on Discrimination Error](https://arxiv.org/html/2611.30220v1#S5.SS2.SSS1). For finite classical distributions, equality in strong subadditivity holds exactly when one of the two outer variables is a function of the middle variable almost surely. The pointwise inequality also holds for unnormalized nonnegative tables, with the same equality condition for every positive parameter.

The [challenge](Challenge.lean) states the three claims using finite sums, products, and the scalar integral from Lemma 3. The [solution](Solution.lean) identifies this integral with the subentropy of a diagonal matrix and applies the published Lean proofs. [Companion proof index](https://pratikpatil.io/lean/subentropy/)

The original code in this package is licensed under [Apache 2.0](LICENSE). The package includes 11 project modules and 27 modules adapted from The Omega Institute. Their contents match the companion's published source ZIP. [Source attribution and upstream license](ATTRIBUTION.md)

## Reproduce the proof check

Use Linux or WSL2 with Git, Python 3, bubblewrap, and the Lean version pinned in [lean-toolchain](lean-toolchain). From this directory, fetch the Mathlib build cache and run the checker.

```sh
lake exe cache get
python3 check.py
```

The [configuration](comparator.json) names all three theorems and fixes the definitions appearing in their statements. The three `sorry` terms in the challenge are the statements for which the solution must provide proofs. The script runs Comparator in its default sandbox with the toolchain's Lean kernel, NanoDa, and con-ron. [Palomar's reference procedure](https://github.com/PalomarRegistry/PalomarTemplate/blob/main/scripts/verify-comparator.sh)

All three kernels accepted the solution with Lean 4.35.0. Each theorem uses only `propext`, `Classical.choice`, and `Quot.sound`. [Verification transcript](comparator.log)
