module

public import SubentropyCertificates.QuadraticPosterior
public import SubentropyCertificates.QuadraticAttainment

/-! The complementary quadratic lower bound and pointwise sharpness
for every prescribed attainable value of the purity difference. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped BigOperators
namespace SubentropyCertificates.Quadratic
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.OrthogonalRecordEntropy
open D5.S3.Quantum.Subentropy.GuessingProbability
open SubentropyCertificates.ClassicalCurve
open SubentropyCertificates.Discrimination
variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]

/-- Proposition prop:quadratic-certificate with n=m+2. The statistic is
half the difference of the average and joint purities. -/
theorem complementary_quadratic_bound (m : ℕ) (hn : Fintype.card X=m+2)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x=1) (ρ : X → DensityState B) :
    let c := statistic p hp hs ρ
    let e := 1-pGuess p ρ
    (0 ≤ c ∧ c ≤ curve m e ∧ inverse m c ≤ e) ∧
    ∀ s ∈ Icc 0 (radius m/2),
      ∃ (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hsw : ∑ x, w x=1) (b : B),
        statistic w hw hsw (fun _ => pointerState b) = s ∧
        1-pGuess w (fun _ => pointerState b) = inverse m s := by
  let c := statistic p hp hs ρ
  let e := 1-pGuess p ρ
  have hc : 0 ≤ c := by
    dsimp [c]
    rw [statistic_eq_gram]
    exact div_nonneg (offSquare_nonneg _) (by norm_num)
  have hce := optimal_quadratic_upper m hn p hp hs ρ
  have he : e ∈ Icc 0 (radius m) := by rw [radius_eq]; exact optimal_error_range m hn p hp hs ρ
  obtain ⟨hin,hval⟩ := inverse_spec m c ⟨hc,hce.trans (curve_le_max m _)⟩
  have hle : inverse m c ≤ e := by
    by_contra! h
    exact (not_lt_of_ge hce) ((curve_strict m he hin h).trans_eq hval)
  have hX : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have : Nonempty B := by
    by_contra h
    have : IsEmpty B := not_nonempty_iff.mp h
    have ht := (ρ (Classical.choice hX)).2.2
    simp [Matrix.trace] at ht
  exact ⟨⟨hc,hce,hle⟩, quadratic_attainment m hn⟩

end SubentropyCertificates.Quadratic
