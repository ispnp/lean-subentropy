module

public import SharpGuessing.Ensemble
public import SubentropyCertificates.CurveInverse
public import SubentropyCertificates.CurveTangent
public import SubentropyCertificates.UniformEndpoint

/-! The challenge and companion curves agree after sending label zero to `none`. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set SubentropyCertificates

namespace SubentropySharpGuessing

theorem maxError_bridge (m : ℕ) : maxError (m + 2) = ClassicalCurve.uniformError m := rfl

theorem phi_bridge (m : ℕ) (e : ℝ) : phi (m + 2) e = ClassicalCurve.phi m e := by
  have hprior : extremalPrior (m + 2) 0 e = ClassicalCurve.extremalVector m e ∘
      finSuccEquiv (m + 1) := by
    funext x
    refine Fin.cases ?_ (fun j ↦ ?_) x
    · simp [extremalPrior, ClassicalCurve.extremalVector]
    · simp [extremalPrior, ClassicalCurve.extremalVector, show (m : ℝ) + 2 - 1 = m + 1 by ring]
  change ClassicalCurve.classicalSubentropy (extremalPrior (m + 2) 0 e) = _
  rw [hprior]
  exact ClassicalCurve.classical_subentropy_reindex _ _

theorem inverse_bridge (m : ℕ) (q : ℝ) (hq : q ∈ Discrimination.curveRange m) :
    phiInverse (m + 2) q = Discrimination.phiInverse m q hq := by
  have hsingleton : {e : ℝ | e ∈ Icc 0 (maxError (m + 2)) ∧ phi (m + 2) e = q} =
      {Discrimination.phiInverse m q hq} := by
    ext e
    simp only [maxError_bridge, phi_bridge, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨he, hq'⟩
      exact Discrimination.phi_preimage_unique m he (Discrimination.phiInverse_mem m q hq)
        (hq'.trans (Discrimination.phi_phiInverse m q hq).symm)
    · rintro rfl
      exact ⟨Discrimination.phiInverse_mem m q hq, Discrimination.phi_phiInverse m q hq⟩
  rw [phiInverse, hsingleton, csInf_singleton]

theorem curve_lt_error {n : ℕ} (hn : 2 ≤ n) (e : ℝ) (he : 0 < e) (hmax : e ≤ maxError n) :
    phi n e < e := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 2 := ⟨n - 2, by omega⟩
  rw [phi_bridge]
  exact ClassicalCurve.phi_lt_error m he (hmax.trans (ClassicalCurve.uniformError_mem m).2)

theorem inverse_on_branch {n : ℕ} (hn : 2 ≤ n) :
    StrictMonoOn (phi n) (Icc 0 (maxError n)) ∧ phi n 0 = 0 ∧
    phi n (maxError n) = Real.log (n : ℝ) - (harmonic n : ℝ) + 1 ∧
    ∀ q ∈ Icc 0 (phi n (maxError n)),
      phiInverse n q ∈ Icc 0 (maxError n) ∧ phi n (phiInverse n q) = q := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 2 := ⟨n - 2, by omega⟩
  simp only [maxError_bridge, phi_bridge]
  refine ⟨?_, ClassicalCurve.phi_zero m, ClassicalCurve.phi_uniform_endpoint m, ?_⟩
  · intro a ha b hb hab
    simpa only [phi_bridge] using ClassicalCurve.phi_strictMono m ha hb hab
  · intro q hq
    rw [inverse_bridge m q hq]
    exact ⟨Discrimination.phiInverse_mem m q hq, Discrimination.phi_phiInverse m q hq⟩

end SubentropySharpGuessing
