module

public import SubentropyCertificates.SpectralVariation
public import SubentropyCertificates.ClassicalContinuity
public import SubentropyCertificates.MarginalPurity

/-! Theorem 13: the upper bound for quantum subentropy on a trace-distance ball.
The spectral modulus is due to Hanson and Datta. We lift the certified classical
maximal-coupling proof via the ordered eigenvalue perturbation inequality. -/
@[expose] public section
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace SubentropyCertificates.SpectralContinuity
open SubentropyCertificates.Continuity
open SubentropyCertificates.ClassicalCurve
open SubentropyCertificates.Subadditivity (subentropy_of_spectrum)
open SubentropyCertificates.MixedQubit (traceDistance)
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.DensityKernel

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Ordering the spectral probability vector preserves subentropy. -/
theorem ordered_spectrum_law (ρ : DensityState D) :
    orderedSpectrum ρ ∈ probabilitySimplex (Fin (Fintype.card D)) ∧
      subentropy ρ = classicalSubentropy (orderedSpectrum ρ) := by
  let hA := (density_posSemidef ρ).isHermitian
  let e : Fin (Fintype.card D) ≃ D := Fintype.equivOfCardEq (Fintype.card_fin _)
  have hid : hA.eigenvalues ∘ e = orderedSpectrum ρ := by
    funext i
    change hA.eigenvalues₀ (e.symm (e i)) = hA.eigenvalues₀ i
    rw [e.symm_apply_apply]
  rw [← hid]
  exact ⟨simplex_reindex _ (spectral_prob (density_posSemidef ρ) ρ.2.2) e,
    (subentropy_of_spectrum hA).trans (classical_subentropy_reindex _ e).symm⟩

/-- The paper's dimension-indexed modulus, zero on a one-dimensional space. -/
def quantumModulus : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, _ => 0
  | m + 2, δ => modulus m δ

private theorem eq_of_small_dimension (ρ σ : DensityState D) (hn : Fintype.card D ≤ 1) :
    subentropy ρ = subentropy σ := by
  have : Subsingleton (Fin (Fintype.card D)) := Fin.subsingleton_iff_le_one.mpr hn
  rw [(ordered_spectrum_law ρ).2, (ordered_spectrum_law σ).2]
  congr 1
  funext i
  have entry (τ : DensityState D) : orderedSpectrum τ i = 1 := by
    have hs := (ordered_spectrum_law τ).1.2
    rwa [Finset.sum_eq_single i (fun j _ hj ↦ (hj (Subsingleton.elim j i)).elim)
      (fun h ↦ (h (Finset.mem_univ i)).elim)] at hs
  exact (entry ρ).trans (entry σ).symm

/-- Upper bound of Theorem 13 for arbitrary density matrices at trace distance at most δ.
The radius may extend beyond the uniform endpoint and the states may be singular. -/
theorem quantum_continuity_upper (ρ σ : DensityState D) {δ : ℝ} (hδ : traceDistance ρ σ ≤ δ) :
    |subentropy ρ - subentropy σ| ≤ quantumModulus (Fintype.card D) δ := by
  by_cases hn : Fintype.card D ≤ 1
  · rw [eq_of_small_dimension ρ σ hn, sub_self, abs_zero]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with h | h <;> simp [h, quantumModulus]
  · obtain ⟨m, hm⟩ : ∃ m, Fintype.card D = m + 2 := ⟨Fintype.card D - 2, by omega⟩
    have hdist := (ordered_spectrum_totalVariation_le ρ σ).trans hδ
    have ht : 0 ≤ totalVariation (orderedSpectrum ρ) (orderedSpectrum σ) :=
      div_nonneg (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (by norm_num)
    rw [(ordered_spectrum_law ρ).2, (ordered_spectrum_law σ).2,
      show quantumModulus (Fintype.card D) δ = modulus m δ by rw [hm]; rfl]
    exact (classical_modulus_isGreatest m (X := Fin (Fintype.card D))
      (by simpa using hm) (ht.trans hdist)).2
      ⟨_, _, (ordered_spectrum_law ρ).1, (ordered_spectrum_law σ).1, hdist, rfl⟩

end SubentropyCertificates.SpectralContinuity
