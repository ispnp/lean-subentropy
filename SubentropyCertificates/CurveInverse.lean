module

public import SubentropyCertificates.OptimalGuessing
public import Mathlib.Topology.Order.IntermediateValue

/-! The genuine inverse on the increasing branch, including both endpoints. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped BigOperators

namespace SubentropyCertificates.Discrimination
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Subentropy.ClassicalQuantumGram
open D5.S3.Quantum.Subentropy.GuessingProbability
open SubentropyCertificates.ClassicalCurve

def curveRange (m : ℕ) : Set ℝ := Icc 0 (phi m (uniformError m))

theorem phi_maps_to_curveRange (m : ℕ) {e : ℝ} (he : e ∈ Icc 0 (uniformError m)) :
    phi m e ∈ curveRange m := by
  have h0 := (phi_strictMono m).monotoneOn
    (show (0 : ℝ) ∈ Icc 0 (uniformError m) from ⟨le_rfl, (uniformError_mem m).1⟩) he he.1
  rw [phi_zero] at h0
  exact ⟨h0, phi_le_uniform_max m ⟨he.1, he.2.trans (uniformError_mem m).2⟩⟩

theorem curveRange_zero (m : ℕ) : (0 : ℝ) ∈ curveRange m := by
  have h := phi_maps_to_curveRange m
    (show (0 : ℝ) ∈ Icc 0 (uniformError m) from ⟨le_rfl, (uniformError_mem m).1⟩)
  simpa only [phi_zero] using h

theorem curveRange_upper (m : ℕ) : phi m (uniformError m) ∈ curveRange m :=
  phi_maps_to_curveRange m ⟨(uniformError_mem m).1, le_rfl⟩

theorem phi_preimage_exists (m : ℕ) {q : ℝ} (hq : q ∈ curveRange m) :
    ∃ e ∈ Icc 0 (uniformError m), phi m e = q := by
  have hsub : Icc (0 : ℝ) (uniformError m) ⊆ Icc (0 : ℝ) 1 :=
    fun _ he => ⟨he.1, he.2.trans (uniformError_mem m).2⟩
  have hc := (phi_continuous m).mono hsub
  have hsurj := hc.surjOn_Icc
    (show (0 : ℝ) ∈ Icc 0 (uniformError m) from ⟨le_rfl, (uniformError_mem m).1⟩)
    (show uniformError m ∈ Icc 0 (uniformError m) from ⟨(uniformError_mem m).1, le_rfl⟩)
  apply hsurj
  simpa only [curveRange, phi_zero] using hq

theorem phi_preimage_unique (m : ℕ) {e f : ℝ}
    (he : e ∈ Icc 0 (uniformError m)) (hf : f ∈ Icc 0 (uniformError m))
    (h : phi m e = phi m f) : e = f :=
  (phi_strictMono m).injOn he hf h

/-- The inverse is defined only with a proof that its argument lies in the
actual range of the increasing branch; no value outside that range is used. -/
def phiInverse (m : ℕ) (q : ℝ) (hq : q ∈ curveRange m) : ℝ :=
  Classical.choose (phi_preimage_exists m hq)

theorem phiInverse_mem (m : ℕ) (q : ℝ) (hq : q ∈ curveRange m) :
    phiInverse m q hq ∈ Icc 0 (uniformError m) :=
  (Classical.choose_spec (phi_preimage_exists m hq)).1

theorem phi_phiInverse (m : ℕ) (q : ℝ) (hq : q ∈ curveRange m) :
    phi m (phiInverse m q hq) = q :=
  (Classical.choose_spec (phi_preimage_exists m hq)).2

theorem phiInverse_phi (m : ℕ) (e : ℝ) (he : e ∈ Icc 0 (uniformError m)) :
    phiInverse m (phi m e) (phi_maps_to_curveRange m he) = e :=
  phi_preimage_unique m (phiInverse_mem m _ _) he (phi_phiInverse m _ _)

theorem phiInverse_zero (m : ℕ) : phiInverse m 0 (curveRange_zero m) = 0 := by
  apply phi_preimage_unique m (phiInverse_mem m _ _)
    (show (0 : ℝ) ∈ Icc 0 (uniformError m) from ⟨le_rfl, (uniformError_mem m).1⟩)
  rw [phi_phiInverse, phi_zero]

theorem phiInverse_upper (m : ℕ) :
    phiInverse m (phi m (uniformError m)) (curveRange_upper m) = uniformError m :=
  phiInverse_phi m _ ⟨(uniformError_mem m).1, le_rfl⟩

theorem phiInverse_strictMono (m : ℕ) {q r : ℝ}
    (hq : q ∈ curveRange m) (hr : r ∈ curveRange m) (hqr : q < r) :
    phiInverse m q hq < phiInverse m r hr := by
  by_contra hn
  have h := (phi_strictMono m).monotoneOn (phiInverse_mem m r hr)
    (phiInverse_mem m q hq) (le_of_not_gt hn)
  rw [phi_phiInverse, phi_phiInverse] at h
  exact (not_le_of_gt hqr) h

variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]

theorem conditional_subentropy_range (m : ℕ) (hn : Fintype.card X = m + 2)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (ρ : X → DensityState B) : conditionalSubentropy p hp hs ρ ∈ curveRange m := by
  have h := optimal_discrimination_bound m hn p hp hs ρ
  exact ⟨h.1, h.2.1.trans (phi_maps_to_curveRange m h.2.2).2⟩

theorem inverse_discrimination_bound (m : ℕ) (hn : Fintype.card X = m + 2)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (ρ : X → DensityState B) :
    phiInverse m (conditionalSubentropy p hp hs ρ) (conditional_subentropy_range m hn p hp hs ρ)
      ≤ 1 - pGuess p ρ := by
  apply error_threshold_lower_bound m hn p hp hs ρ _ (phiInverse_mem m _ _)
  exact (phi_phiInverse m _ _).le

end SubentropyCertificates.Discrimination
