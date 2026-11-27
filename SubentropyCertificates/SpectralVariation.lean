module

public import SubentropyCertificates.OrderedEigenvalues
public import SubentropyCertificates.QubitTraceDistance
public import SubentropyCertificates.MaximalCoupling
import all SubentropyCertificates.HelstromSpectral

/-! The trace-norm eigenvalue perturbation inequality. A common upper bound for
two Hermitian matrices is obtained from the positive part of their difference. -/
@[expose] public section
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace SubentropyCertificates.SpectralContinuity
open SubentropyCertificates.Helstrom
open SubentropyCertificates.Continuity
open SubentropyCertificates.MixedQubit (traceDistance)
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation

variable {D : Type*} [Fintype D] [DecidableEq D]

private theorem sum_ordered {A : Matrix D D ℂ} (hA : A.IsHermitian) :
    ∑ i, hA.eigenvalues₀ i = A.trace.re := by
  let e : Fin (Fintype.card D) ≃ D := Fintype.equivOfCardEq (Fintype.card_fin _)
  have hs := congrArg Complex.re hA.trace_eq_sum_eigenvalues
  simp only [Complex.re_sum] at hs
  exact (e.symm.sum_comp hA.eigenvalues₀).symm.trans hs.symm

/-- Trace-norm perturbation inequality for decreasingly ordered eigenvalues
of arbitrary Hermitian matrices, including matrices with repeated eigenvalues. -/
theorem ordered_spectral_l1_le {A B : Matrix D D ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (∑ i, |hA.eigenvalues₀ i - hB.eigenvalues₀ i|) ≤ ∑ i, |(hA.sub hB).eigenvalues i| := by
  let hH := hA.sub hB
  let w := hH.eigenvalues
  let f := fun i ↦ (|w i| + w i) / 2
  let g := fun i ↦ (|w i| - w i) / 2
  let U := hH.eigenvectorUnitary
  let P := spectralMatrix U f
  let N := spectralMatrix U g
  have hP : P.PosSemidef := spectral_pos U f (fun i ↦ by dsimp [f]; linarith [neg_abs_le (w i)])
  have hN : N.PosSemidef := spectral_pos U g (fun i ↦ by dsimp [g]; linarith [le_abs_self (w i)])
  have hd : A - B = P - N := by
    rw [show P - N = _ from spectral_sub U f g]
    calc
      _ = spectralMatrix U w := hH.spectral_theorem
      _ = _ := congrArg (spectralMatrix U) (funext fun i ↦ by dsimp [f, g]; ring)
  let C := B + P
  have hC : C.IsHermitian := hB.add hP.isHermitian
  have ca : C - A = N := by
    change B + P - A = N
    rw [sub_eq_iff_eq_add.mp hd]
    abel
  have cb : C - B = P := by dsimp [C]; abel
  have ha := ordered_eigenvalues_mono hA hC (by rwa [ca])
  have hb := ordered_eigenvalues_mono hB hC (by rwa [cb])
  have point i : |hA.eigenvalues₀ i - hB.eigenvalues₀ i| ≤
      (hC.eigenvalues₀ i - hA.eigenvalues₀ i) + (hC.eigenvalues₀ i - hB.eigenvalues₀ i) :=
    abs_le.mpr ⟨by linarith [hb i], by linarith [ha i]⟩
  calc
    _ ≤ _ := Finset.sum_le_sum (fun i _ ↦ point i)
    _ = N.trace.re + P.trace.re := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_ordered]
      rw [← ca, ← cb, Matrix.trace_sub, Matrix.trace_sub, Complex.sub_re, Complex.sub_re]
    _ = _ := by
      rw [show N.trace.re = _ from spectral_trace U g, show P.trace.re = _ from spectral_trace U f,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ ↦ by change g i + f i = |w i|; dsimp [g, f]; ring)

/-- The probability vector of eigenvalues in decreasing order. -/
def orderedSpectrum (ρ : DensityState D) : Fin (Fintype.card D) → ℝ :=
  (density_posSemidef ρ).isHermitian.eigenvalues₀

/-- Total variation of the two ordered spectra is bounded by quantum trace distance. -/
theorem ordered_spectrum_totalVariation_le (ρ σ : DensityState D) :
    totalVariation (orderedSpectrum ρ) (orderedSpectrum σ) ≤ traceDistance ρ σ :=
  div_le_div_of_nonneg_right
    (ordered_spectral_l1_le (density_posSemidef ρ).isHermitian (density_posSemidef σ).isHermitian)
    (by norm_num)

end SubentropyCertificates.SpectralContinuity
