module

public import SubentropyCertificates.QubitTraceDistance

/-! Trace distance varies continuously with the two finite density
matrices, by its variational characterization over a compact effect set. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder
namespace SubentropyCertificates.CompactStability
open D5.S3.Quantum.Foundation.FiniteStateChannel
open SubentropyCertificates.Discrimination
open SubentropyCertificates.MixedQubit (traceDistance traceDistance_test)
open SubentropyCertificates.BinarySpectra (densityMatrix)
variable {D : Type*} [Fintype D] [DecidableEq D]

theorem traceDistance_nonneg (ρ σ : DensityState D) : 0 ≤ traceDistance ρ σ := by
  unfold traceDistance; positivity

theorem traceDistance_self (ρ : DensityState D) : traceDistance ρ ρ=0 := by
  obtain ⟨E,_,_,h,_⟩ := traceDistance_test ρ ρ
  simpa only [sub_self,Matrix.mul_zero,Matrix.trace_zero,Complex.zero_re] using h.symm

theorem traceDistance_continuous {T : Type*} [TopologicalSpace T] (ρ σ : T → DensityState D)
    (hρ : Continuous (fun t => densityMatrix (ρ t))) (hσ : Continuous (fun t => densityMatrix (σ t))) :
    Continuous (fun t => traceDistance (ρ t) (σ t)) := by
  let f (t : T) (E : Matrix D D ℂ) := (E*(densityMatrix (ρ t)-densityMatrix (σ t))).trace.re
  have hc : Continuous ↿f := by
    have h : Continuous (fun z : T × Matrix D D ℂ => z.2 *
        (densityMatrix (ρ z.1)-densityMatrix (σ z.1))) :=
      continuous_snd.mul ((hρ.sub hσ).comp continuous_fst)
    exact Complex.continuous_re.comp (by fun_prop (disch := assumption))
  have hs (t : T) : sSup (f t '' Icc 0 1) = traceDistance (ρ t) (σ t) := by
    apply IsGreatest.csSup_eq
    obtain ⟨E,hE,hC,hval,hmax⟩ := traceDistance_test (ρ t) (σ t)
    refine ⟨⟨E,⟨hE.nonneg,sub_nonneg.mp hC.nonneg⟩,hval⟩,?_⟩
    rintro _ ⟨F,hF,rfl⟩
    exact (hmax F (Matrix.nonneg_iff_posSemidef.mp hF.1)
      (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hF.2))).trans_eq hval
  simpa only [hs] using (isCompact_effect_interval (B := D)).continuous_sSup hc

end SubentropyCertificates.CompactStability
