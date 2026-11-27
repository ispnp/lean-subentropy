# Source attribution

The 11 modules in `SubentropyCertificates/` are the sources needed by
`SubentropyCertificates.ClassicalStrongSubadditivity` in release 1 of Pratik Patil's
*Quantum Subentropy: Subadditivity and Sharp Bounds on Discrimination Error* Lean project.
The pilot preserves their source bytes. [Lean companion](https://pratikpatil.io/lean/subentropy/)

The 27 modules in `vendor/upstream/module_snapshot/D5/` are drawn from The Omega Institute's
`trureturing` at revision `d3e1e931e66ad4a3f54c95ef96cf723edcd7e792`. The proof release
adapted module imports and visibility for Lean 4.35.0. The pilot preserves those adaptations.
The included record gives the SHA-256 hashes of each original and adapted file.
[Upstream revision](https://github.com/the-omega-institute/trureturing/tree/d3e1e931e66ad4a3f54c95ef96cf723edcd7e792)
 · [Adaptation record](vendor/upstream/module_adaptation.json) · [Apache 2.0 license](vendor/upstream/LICENSE)

`SubentropyCertificates/PinchingUpper.lean` also credits the upstream proof of the private
lemma `pinching_upper` in `Subadditivity.lean`. Its port exposes the bound as
`pinching_gap_le_label_subentropy` and carries the same Apache 2.0 license.
[Ported proof](SubentropyCertificates/PinchingUpper.lean)
