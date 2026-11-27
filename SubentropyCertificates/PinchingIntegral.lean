module
public import D5.S3.Quantum.Subentropy.PinchingGap
import all D5.S3.Quantum.Subentropy.PinchingGap

/-! Equality in the integrated pinching inequality implies pointwise equality
on the entire Gaussian space, including the null hyperplanes used below.
The sign-orbit integral representation and convexity are from the pinned
Omega Institute library. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexOrder MatrixOrder
namespace SubentropyCertificates.PinchingEquality
open D5.S3.Quantum.Subentropy.GaussianQuadratic
open D5.S3.Quantum.Subentropy.EntropyJensenGap
open D5.S3.Quantum.Subentropy.PinchingGap
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.ClassicalQuantumGram

private theorem gaussian_full_support {D : Type*} [Fintype D] :
    (stdGaussian (EuclideanSpace ℂ D)).IsOpenPosMeasure := by
  let : (gaussianReal 0 1).IsOpenPosMeasure :=
    (gaussianReal_absolutelyContinuous' 0 one_ne_zero).isOpenPosMeasure
  classical
  rw [← (complex_coordinate_transport (ι := D)).1]
  apply Continuous.isOpenPosMeasure_map
  · unfold complexGaussianCoordinates
    simp_rw [Complex.mk_eq_add_mul_I]
    fun_prop
  · intro z
    refine ⟨fun p => if p.2 = 0 then (z p.1).re else (z p.1).im, ?_⟩
    apply PiLp.ext
    intro i
    simp [complexGaussianCoordinates]

variable {X B I : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B] [Fintype I]

def gain (A : Matrix (X × B) (X × B) ℂ) : ℝ :=
  matrixSubentropy (blockPinch A) - matrixSubentropy A

def orbit (A : Matrix (X × B) (X × B) ℂ) (z : EuclideanSpace ℂ (X × B)) (s : X → Bool) : ℝ :=
  gaussianQuadratic (signUnitary s * A * (signUnitary s).conjTranspose) z

private theorem orbit_continuous (A : Matrix (X × B) (X × B) ℂ) :
    Continuous (signOrbitEntropyGap A) := by
  have hc (M : Matrix (X × B) (X × B) ℂ) : Continuous (gaussianQuadratic M) :=
    (Complex.continuous_re.comp (continuous_id.inner (Matrix.toEuclideanLin M).continuous_of_finiteDimensional)).div_const 2
  unfold signOrbitEntropyGap finiteAverage
  fun_prop (disch := exact hc _)

theorem orbit_sum (w : I → ℝ) (A : I → Matrix (X × B) (X × B) ℂ)
    (z : EuclideanSpace ℂ (X × B)) (s : X → Bool) :
    orbit (∑ i, w i • A i) z s = ∑ i, w i * orbit (A i) z s := by
  simp only [orbit, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    quadratic_sum, quadratic_real_smul]

theorem orbit_gap_eq_of_gain_eq (i₀ : X × B) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i = 1) (A : I → Matrix (X × B) (X × B) ℂ)
    (hA : ∀ i, (A i).PosSemidef) (htr : ∀ i, (A i).trace = 1)
    (he : gain (∑ i, w i • A i) = ∑ i, w i * gain (A i)) (z : EuclideanSpace ℂ (X × B)) :
    entropyJensenGap (fun s => ∑ i, w i * orbit (A i) z s) =
      ∑ i, entropyJensenGap (fun s => w i * orbit (A i) z s) := by
  let T := ∑ i, w i • A i
  have hT : T.PosSemidef := Matrix.posSemidef_sum _ (fun i _ => (hA i).smul (hw i))
  have htrace : T.trace = 1 := by
    simp only [T, Matrix.trace_sum, Matrix.trace_smul, htr, Complex.real_smul, mul_one,
      ← Complex.ofReal_sum, hs, Complex.ofReal_one]
  let γ := stdGaussian (EuclideanSpace ℂ (X × B))
  let f (z : EuclideanSpace ℂ (X × B)) := ∑ i, w i * signOrbitEntropyGap (A i) z
  let g := signOrbitEntropyGap T
  have hi (i : I) := pinch_gap_integral (A i) (hA i) (htr i) i₀
  have ht := pinch_gap_integral T hT htrace i₀
  have hf : Integrable f γ := integrable_finsetSum _ (fun i _ => (hi i).1.const_mul _)
  have hle (u : EuclideanSpace ℂ (X × B)) : g u ≤ f u :=
    (sign_orbit_gap_convex u).map_sum_le (fun i _ => hw i) hs (fun i _ => hA i)
  have hInt : ∫ u, f u - g u ∂γ = 0 := by
    rw [integral_sub hf ht.1]
    unfold f
    rw [integral_finsetSum _ (fun i _ => (hi i).1.const_mul _)]
    simp_rw [integral_const_mul]
    change (∑ i, w i * ∫ u, signOrbitEntropyGap (A i) u ∂γ) - ∫ u, signOrbitEntropyGap T u ∂γ = 0
    dsimp only [γ]
    simp_rw [← fun i => (hi i).2]
    rw [← ht.2]
    exact sub_eq_zero.mpr he.symm
  have hae := (integral_eq_zero_iff_of_nonneg (fun u => sub_nonneg.mpr (hle u)) (hf.sub ht.1)).mp hInt
  let : γ.IsOpenPosMeasure := gaussian_full_support
  have hfC : Continuous f := continuous_finsetSum _ (fun i _ => continuous_const.mul (orbit_continuous _))
  have hpoint := congrFun (Measure.eq_of_ae_eq hae (hfC.sub (orbit_continuous _)) continuous_const) z
  have hfg : g z = f z := (sub_eq_zero.mp hpoint).symm
  have hstate (M : Matrix (X × B) (X × B) ℂ) (hM : M.PosSemidef) :
      signOrbitEntropyGap M z = entropyJensenGap (orbit M z) :=
    (sign_orbit_entropy_laws M hM z).2.2.1
  change signOrbitEntropyGap T z = ∑ i, w i * signOrbitEntropyGap (A i) z at hfg
  rw [hstate T hT] at hfg
  simp_rw [fun i => hstate (A i) (hA i)] at hfg
  simp_rw [fun i => entropyJensenGap_laws.2.1 (w i) (orbit (A i) z) (hw i)]
  simpa only [T, funext (orbit_sum w A z)] using hfg

end SubentropyCertificates.PinchingEquality
