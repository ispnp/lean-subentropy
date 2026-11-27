module
public import SubentropyCertificates.PinchingRank
public import SubentropyCertificates.PosteriorRefinement
public import SubentropyCertificates.PureGramSignals

/-! Necessity at positive conditional subentropy in the measurement
comparison. The pure decomposition is constructed from the given effects. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
namespace SubentropyCertificates.PinchingEquality
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Subentropy.ClassicalQuantumGram
open D5.S3.Quantum.Subentropy.PinchingGap
open SubentropyCertificates.MeasurementPosterior
open SubentropyCertificates.Discrimination
open SubentropyCertificates.ClassicalCurve
open SubentropyCertificates.QuantumEquality
variable {X B Y : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B] [Fintype Y]

theorem gram_projector_of_positive_posterior_equality (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : X → DensityState B) (F : Y → Matrix B B ℂ)
    (hF : ∀ y, (F y).PosSemidef) (hsF : ∑ y, F y = 1)
    (hpos : 0 < conditionalSubentropy p hp hs ρ)
    (he : conditionalSubentropy p hp hs ρ = posteriorAverage p ρ F) :
    ∃ v, amplitude v v = 1 ∧ (cqRowSqrt p ρ).conjTranspose * cqRowSqrt p ρ = projector v := by
  classical
  have hX : Nonempty X := by
    by_contra h
    have : IsEmpty X := not_nonempty_iff.mp h
    simp at hs
  let x₀ := Classical.choice hX
  have hB : Nonempty B := by
    by_contra h
    have : IsEmpty B := not_nonempty_iff.mp h
    have ht := (ρ x₀).2.2
    simp [Matrix.trace] at ht
  let i₀ : X × B := (x₀, Classical.choice hB)
  let M := cqRowSqrt p ρ
  let G y := effectGram p ρ (F y)
  have ht : ∑ y, G y = M.conjTranspose * M := sum_effectGram p ρ F hsF
  have htrace : (∑ y, G y).trace = 1 := by rw [ht]; exact gram_trace_one p hp hs ρ
  obtain ⟨w, hw, hws, v, hv, hdec, hub⟩ := refinement_of_gram_pieces G
    (fun y => effectGram_posSemidef p ρ _ (hF y)) htrace x₀
  have hgram := ht.symm.trans hdec
  have hcond : conditionalSubentropy p hp hs ρ = gain (∑ i, w i • projector (v i)) :=
    (cq_conditional_eq_pinchingGap p hp hs ρ).trans (congrArg gain hgram)
  have hupper : ∑ i, w i * gain (projector (v i)) ≤ posteriorAverage p ρ F := by
    have hb y : labelPosterior (G y) = posterior p ρ (F y) := by
      funext x
      simp only [G, labelPosterior, posterior, mass_effectGram p hp ρ, labelMass_effectGram p hp ρ]
    simpa only [posteriorAverage, hb, G, mass_effectGram p hp ρ] using hub
  have hstates i : (projector (v i)).PosSemidef ∧ (projector (v i)).trace = 1 := by
    refine ⟨Matrix.posSemidef_vecMulVec_self_star _, ?_⟩
    change (∑ k, v i k * star (v i k)) = 1
    simpa only [amplitude, dotProduct, Pi.star_apply, mul_comm] using hv i
  have hlo : gain (∑ i, w i • projector (v i)) ≤ ∑ i, w i * gain (projector (v i)) :=
    (actual_pinching_gap_laws i₀).1.map_sum_le (fun i _ => hw i) hws (fun i _ => hstates i)
  obtain ⟨u, hu, hP⟩ := projector_of_positive_gain_equality i₀ w hw hws v hv
    (hpos.trans_eq hcond) (le_antisymm hlo (hupper.trans_eq (he.symm.trans hcond)))
  exact ⟨u, hu, hgram.trans hP⟩

theorem gram_rank_one_of_positive_posterior_equality (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : X → DensityState B) (F : Y → Matrix B B ℂ)
    (hF : ∀ y, (F y).PosSemidef) (hsF : ∑ y, F y = 1)
    (hpos : 0 < conditionalSubentropy p hp hs ρ)
    (he : conditionalSubentropy p hp hs ρ = posteriorAverage p ρ F) :
    ((cqRowSqrt p ρ).conjTranspose * cqRowSqrt p ρ).rank = 1 := by
  obtain ⟨v, hv, hG⟩ := gram_projector_of_positive_posterior_equality p hp hs ρ F hF hsF hpos he
  rw [hG, projector_rank_one _ hv]

theorem positive_posterior_equality_iff (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hs : ∑ x, p x = 1) (ρ : X → DensityState B) (F : Y → Matrix B B ℂ)
    (hF : ∀ y, (F y).PosSemidef) (hsF : ∑ y, F y = 1)
    (hpos : 0 < conditionalSubentropy p hp hs ρ) :
    conditionalSubentropy p hp hs ρ = posteriorAverage p ρ F ↔
      ∃ (u : B → ℂ) (hu : ∑ b, star (u b) * u b = 1),
        ∀ x, 0 < p x → ρ x = pureSignal u hu := by
  constructor
  · intro he
    obtain ⟨v, hv, hG⟩ := gram_projector_of_positive_posterior_equality p hp hs ρ F hF hsF hpos he
    exact common_pure_signal_of_gram_projector p hp ρ v hv hG
  · rintro ⟨u, hu, h⟩
    exact posterior_equality_of_identical_pure_on_support p hp hs ρ u hu h F hF hsF

end SubentropyCertificates.PinchingEquality
